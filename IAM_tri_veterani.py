
import re
import sys

kongruence = u"\u224c"

for zadane_cislo in range(1, 1001):
    cislo = zadane_cislo
    pre_nasobitel = 1

    print(f"Výpočet pro číslo {cislo}:\n")

    # odstraneni pocatecnich nul
    while cislo % 10 == 0:
        cislo //= 10
        print("Odstranění koncové nuly, zadané číslo po úpravě =", cislo)

    # nulovani dokud je to mozne 
    while True:
        if cislo % 10 == 2 or cislo % 10 == 4 or cislo % 10 == 8 or cislo % 10 == 6:
            pre_nasobitel *= 5
            cislo *= 5
            cislo //= 10
            print("Vynásobení zadaného čísla 5 a odstranění koncové nuly, číslo po úpravě =", cislo)
        elif cislo % 10 == 5:
            pre_nasobitel *= 2
            cislo *= 2
            cislo //= 10
            print("Vynásobení zadaného čísla 2 a odstranění koncové nuly, číslo po úpravě =", cislo)
        else:
            break


    # mezery pro zarovnani vypisu
    mezera = ""
    delka_cisla = len(str(cislo))
    while delka_cisla:
        mezera += " "
        delka_cisla -= 1

    nasobitel = []
    zbytek = 1
    stary_zbytek = 0
    n = 1

    print(f"{mezera}                                přebytek1 = 0")
    print(f"         0 + {cislo}*x1 {kongruence} 1")
    print(f"             {cislo}*x1 {kongruence} 1 -> ", end='')

    # hledani kongruence s 1
    while True:
        for i in range(1, 11):
            if (cislo * i) % 10 == zbytek:
                break
            
        i = i % 10
        nasobitel.append(str(i))
        print(f"x{n} = {i}, přebytek{n+1} = ({cislo}*{i} + {stary_zbytek})/10 = ", end='')
        stary_zbytek = (cislo * i + stary_zbytek) // 10
        print(stary_zbytek)

        zbytek = 1 if stary_zbytek % 10 == 0 else 11 - stary_zbytek % 10

        if stary_zbytek == 0:
            break

        n += 1
        formated = "{:10d}".format(stary_zbytek)
        print(f"{formated} + {cislo}*x{n} {kongruence} 1")
        print(f"             {cislo}*x{n} {kongruence} {zbytek % 10} -> ", end='')


    print("")
    vysledek = int("".join(reversed(nasobitel))) * (10 if pre_nasobitel == 1 else pre_nasobitel)
    print(f"Hledaný přirozený násobitel čísla {zadane_cislo} je číslo {vysledek}.")

    zkouska = vysledek * zadane_cislo
    if re.match(r"^1+0+$", str(zkouska)):
        print("Zkouška =", zkouska, "OK")
    else:
        print("Zkouška =", zkouska, "CHYBA", file=sys.stderr)
    
    print()
    print("=======================================================================================")

