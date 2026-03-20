# Kompilator Języka Latte
## 27.11.2023 - Frontend

Kompilator został napisany w Haskellu z wykorzysatniem parsera gramatyki **BNFC** oraz standardowych bibliotek Haskella (StateT, ExceptT, ReaderT, Data.Map, System, etc.)

### Struktura projektu
|           |                   | Opis |
| --------- | :---------------- | :----|
|**src/**   |                   | Pliki źródłowe
|           | Common.hs         | Wspóldzielone często używane definicje
|           | Intermediate.hs   | Kod źródłowy frontendu
|           | Main.hs           | Kod źródłowy funkcji Main i uruchomienia obliczeń
|           | Types.hs          | Definicje typów w kompilatorze
|           | Makefile          | Plik Makefile tworzący rozwiązanie
|           | grammar.cf        | Gramatyka języka Latte + wszsytkie rozszerzenie
| **lib/**  |                   | Biblioteki i skrypty
|           | bnfc              | Link do pliku wykonywalnego programu bnfc -> /home/students/inf/PUBLIC/bin/bncf

### Uruchomienie
Wystarczy wywołać polecenie *make* w korzeniu projketu

W przypadku problemów z bnfc można wywołać polecenie *make BNFC=/ścieżka/do/bnfc*

#### Czyszczenie
Polecenie *make clean* usunie wszelkie pliki utowrzone przez wcześniejsze wywołanie *make*

## 15.01.2024 - Backend

Kompilator języka Latte do kodu maszynowego x86 w wersji 64 bitowej.
Aktualnie nie zostały zaimplementowane żadne rozszerzenia czy optymalizacje.
Generowany kod używa natomiast rejestrów, używają algorytmu symulacji stanu
maszyny docelowej. Przypisania na martwe zmienne są omijane w kodzie docelowym.

Kompilator najpierw tłumaczy kod wejściowy na kod czwórkowy.
Następnie przetwarza kod czwórkowy do grafu przepływu sterowania.
Dalej przeprowadzana jest transformacja do postaci SSA (z operacją kopi).
Następnie dla gotowego kodu SSA przeprowadzana jest analiza żywotności zmienych.
A na koniec symulowany jest stan maszyny docelowej, gdzie na łączeniu bloków
grafu przepływu sterowania dokonywana jest unifkiacja stanu wejścioweg z stanem
końcowym, co w niektórych przypadkach oszczędza zapisów do pamięci.

Pozostaje jeszcze wiele optymalizacji do zrobienia, natomiast aktualnie
kompilator generuje poprawny kod dla wszystkich 32 przykładów.

### Nowa Struktura projektu
|           |                       | Opis |
| --------- | :-------------------- | :----|
|**src/**   |                       | Pliki źródłowe
|           | Common.hs             | Wspóldzielone często używane definicje
|           | Debugging.hs          | Definicje funkcji do debugowania
|           | Intermediate.hs       | Kod źródłowy frontendu
|           | Main.hs               | Kod źródłowy funkcji Main i uruchomienia obliczeń
|           | Machine.hs            | Kod źródłowy procedur generacji kodu x86_64
|           | SSATransformations.hs | Kod żródłowy tworzenia CFG oraz transformacji do SSA.
|           | Types.hs              | Definicje typów w kompilatorze
|           | Makefile              | Plik Makefile tworzący rozwiązanie
|           | grammar.cf            | Gramatyka języka Latte + wszsytkie rozszerzenie
| **lib/**  |                       | Biblioteki i skrypty
|           | bnfc                  | Link do pliku wykonywalnego programu bnfc -> /home/students/inf/PUBLIC/bin/bncf
|           | libinternals.c        | Kod źródłowy w języku C funkcji bilbiotecznych języka Latte: printInt, error, etc.
|           | libinternals.h        | Plik nagłówkowy funkcji biliotecznych
|           | libinternals.o        | Plik obiektowy do łączenia biblioteki z wygenerowanym kodem.

### Generowanie pliku wykonywalnego
Po utworzeniu kodu x86_64 kompilator wykonuje trzy polecenia:
- `nasm -g -f elf64 <nazwa_podstawowa.s> -o <nazwa_podstawowa.o>`
- `gcc -g -Wall -z noexecstack <ścieżka/do/libinternals.c> <nazwa_podstawowa.o> -o <nazwa_podstawowa>`
- `rm <nazwa_podstawowa.o>`,

gdzie `nazwa_podstawowa` to nazwa bez rozszerzenia pliku wejściowego .lat.



## 30.01.2024 - Rozszerzenia

Kompilator obsługuje teraz dodatkowo: 
- tablice,
- struktury,
- obiekty 
- oraz metody wirtualne.

Poprawnie przechodzi wszystkie testy w katalogu `extensions/*`.

Kod maszynowy został delikatnie poprawiony względem poprzedniej wersji.
Kompilator teraz wykonuje znacząco mniej niepotrzebnych odesłań do pamięci oraz
poprawnie zarząda rejestrami nieultonymi podczas wywołania procedury `call`.

Generowany kod maszynowy jest teraz listą typów algebraicznych zamiast zwykłych
napisów, przez co optymalizacje pracujące na wygenerowanym kodzie są prostsze do
implementacji.

Niestety generowany kod maszynowy nie jest poddawany takim optymalizacjom jak
LCSE/GCSE przez co zestawy instrukcji jak:
```
    lea rax, QWORD [...]
    mov rdi, [rax]
```
są skrupulatnie generowane za każdym odwołaniem do pola obiektu, mimo że w 
większości przypadków możnaby zamienić je na
```
    mov rdi, QWORD [...]
```

#### Wykonane części kompilatora
| Kategoria             | max pkt.  |
|:------------------    | -----     |
| Pełny frontend        | 4 pkt.    |
| Pełny backend x86-64  | 10 pkt.   |
| Użycie rejestrów - symulacja stanu maszyny    | 5 pkt.
| **Rozszerzenia:** Tablice | 1 pkt. |
| **Rozszerzenia:** Struktury | 2 pkt. |
| **Rozszerzenia:** Obiekty | 4 pkt. (x86)
| **Rozszerzenia:** Metody wirutalne | 4 pkt. (x86)
| -------------------------------------------- | --------------------- |
| Razem możliwych:  | 30 pkt.
| Kara za opóźnienie: | 4 pkt. (2 x 1tyg)
| Max do zdobycia:  | 26 pkt.
