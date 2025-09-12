# Clue 3: The person who has an average height is directly left of the rabbit owner.
rabbit_idx = idx(animals, 'rabbit')
for i in range(1, n):
    s.add(Implies(animal_vars[i] == rabbit_idx, height_vars[i-1] == avg_height_idx))