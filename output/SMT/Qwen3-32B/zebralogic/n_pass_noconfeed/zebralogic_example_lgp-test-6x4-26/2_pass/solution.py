# Clue 16: Bird and Modern are two apart
clue16 = z3.Or()
for i in range(6):
    for j in range(6):
        if abs(i - j) == 2:
            clue16 = z3.Or(clue16, z3.And(pets[i] == 0, styles[j] == 2))
s.add(clue16)