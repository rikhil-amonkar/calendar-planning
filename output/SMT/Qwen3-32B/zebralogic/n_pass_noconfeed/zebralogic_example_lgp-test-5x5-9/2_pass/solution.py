for i in range(4):  # Eric can't be in the 5th house (index 4)
    s.add(Implies(eric_pos == i, drink[i + 1] == tea))