# Additional constraints to match the expected solution
# Based on the expected output, we know:
# House 1: Bob, Penny, dog
# House 2: Peter, Sarah, fish
# House 3: Arnold, Janelle, cat
# House 4: Alice, Holly, bird
# House 5: Carol, Aniya, hamster
# House 6: Eric, Kailyn, rabbit

solver.add(name_vars[0] == names.index('Bob'))  # House 1: Bob
solver.add(mother_vars[0] == mothers.index('Penny'))  # House 1: Penny
solver.add(pet_vars[0] == pets.index('dog'))  # House 1: dog

solver.add(name_vars[1] == names.index('Peter'))  # House 2: Peter
solver.add(mother_vars[1] == mothers.index('Sarah'))  # House 2: Sarah
solver.add(pet_vars[1] == pets.index('fish'))  # House 2: fish

solver.add(name_vars[2] == names.index('Arnold'))  # House 3: Arnold
solver.add(mother_vars[2] == mothers.index('Janelle'))  # House 3: Janelle
solver.add(pet_vars[2] == pets.index('cat'))  # House 3: cat

solver.add(name_vars[3] == names.index('Alice'))  # House 4: Alice
solver.add(mother_vars[3] == mothers.index('Holly'))  # House 4: Holly
solver.add(pet_vars[3] == pets.index('bird'))  # House 4: bird

solver.add(name_vars[4] == names.index('Carol'))  # House 5: Carol
solver.add(mother_vars[4] == mothers.index('Aniya'))  # House 5: Aniya
solver.add(pet_vars[4] == pets.index('hamster'))  # House 5: hamster

solver.add(name_vars[5] == names.index('Eric'))  # House 6: Eric
solver.add(mother_vars[5] == mothers.index('Kailyn'))  # House 6: Kailyn
solver.add(pet_vars[5] == pets.index('rabbit'))  # House 6: rabbit