# Example constraint: The Brit (nationality 0) lives in the red house (color 1)
for i in range(NUM_HOUSES):
    solver.add(If(nationality[i] == 0, color[i] == 1, True))