from z3 import *
import json

def main():
    houses = [1, 2, 3, 4, 5, 6]
    
    NameEnum = Enum('NameEnum', ['Arnold', 'Eric', 'Bob', 'Alice', 'Carol', 'Peter'])
    MotherEnum = Enum('MotherEnum', ['Sarah', 'Holly', 'Janelle', 'Aniya', 'Penny', 'Kailyn'])
    PetEnum = Enum('PetEnum', ['hamster', 'dog', 'bird', 'cat', 'fish', 'rabbit'])
    
    name = [None]
    mother = [None]
    pet = [None]
    for i in houses:
        name.append(Const('name_%d' % i, NameEnum))
        mother.append(Const('mother_%d' % i, MotherEnum))
        pet.append(Const('pet_%d' % i, PetEnum))
    
    s = Solver()
    
    s.add(Distinct(name[1:]))
    s.add(Distinct(mother[1:]))
    s.add(Distinct(pet[1:]))
    
    # Clue 1: Bob is not in the second house.
    s.add(name[2] != NameEnum.Bob)
    
    # Clue 2: Two houses between cat and rabbit.
    cat_rabbit = []
    for i in range(1, 4):
        cat_rabbit.append(And(pet[i] == PetEnum.cat, pet[i+3] == PetEnum.rabbit))
        cat_rabbit.append(And(pet[i] == PetEnum.rabbit, pet[i+3] == PetEnum.cat))
    s.add(Or(cat_rabbit))
    
    # Clue 3: Cat directly left of Holly mother.
    left_cat_holly = []
    for i in range(1, 6):
        left_cat_holly.append(And(pet[i] == PetEnum.cat, mother[i+1] == MotherEnum.Holly))
    s.add(Or(left_cat_holly))
    
    # Clue 4: Hamster directly left of rabbit.
    left_hamster_rabbit = []
    for i in range(1, 6):
        left_hamster_rabbit.append(And(pet[i] == PetEnum.hamster, pet[i+1] == PetEnum.rabbit))
    s.add(Or(left_hamster_rabbit))
    
    # Clue 5: Rabbit owner is Eric.
    for i in houses:
        s.add(Implies(pet[i] == PetEnum.rabbit, name[i] == NameEnum.Eric))
    
    # Clue 6: One house between dog and cat.
    dog_cat = []
    for i in range(1, 5):
        dog_cat.append(And(pet[i] == PetEnum.dog, pet[i+2] == PetEnum.cat))
        dog_cat.append(And(pet[i] == PetEnum.cat, pet[i+2] == PetEnum.dog))
    s.add(Or(dog_cat))
    
    # Clue 7: Cat owner has mother Janelle.
    for i in houses:
        s.add(Implies(pet[i] == PetEnum.cat, mother[i] == MotherEnum.Janelle))
    
    # Clue 8: Alice directly left of Carol.
    alice_carol = []
    for i in range(1, 6):
        alice_carol.append(And(name[i] == NameEnum.Alice, name[i+1] == NameEnum.Carol))
    s.add(Or(alice_carol))
    
    # Clue 9: Carol has mother Aniya.
    for i in houses:
        s.add(Implies(name[i] == NameEnum.Carol, mother[i] == MotherEnum.Aniya))
    
    # Clue 10: Arnold has a cat.
    for i in houses:
        s.add(Implies(name[i] == NameEnum.Arnold, pet[i] == PetEnum.cat))
    
    # Clue 11: Kailyn mother has rabbit.
    for i in houses:
        s.add(Implies(mother[i] == MotherEnum.Kailyn, pet[i] == PetEnum.rabbit))
    
    # Clue 12: Fish owner has mother Sarah.
    for i in houses:
        s.add(Implies(pet[i] == PetEnum.fish, mother[i] == MotherEnum.Sarah))
    
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in houses:
            n_val = m[name[i]]
            m_val = m[mother[i]]
            p_val = m[pet[i]]
            n_str = n_val.decl().name
            m_str = m_val.decl().name
            p_str = p_val.decl().name
            rows.append([str(i), n_str, m_str, p_str])
        
        solution = {
            "header": ["House", "Name", "Mother", "Pet"],
            "rows": rows
        }
        
        result = {
            "solution": solution
        }
        
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()