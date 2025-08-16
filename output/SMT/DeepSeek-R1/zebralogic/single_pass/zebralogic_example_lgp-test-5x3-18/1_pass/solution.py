from z3 import *
import json

def main():
    # Define the enums for Name, Flower, Animal
    Name = Datatype('Name')
    Name.declare('Alice')
    Name.declare('Eric')
    Name.declare('Arnold')
    Name.declare('Bob')
    Name.declare('Peter')
    Name = Name.create()
    
    Flower = Datatype('Flower')
    Flower.declare('tulips')
    Flower.declare('roses')
    Flower.declare('lilies')
    Flower.declare('daffodils')
    Flower.declare('carnations')
    Flower = Flower.create()
    
    Animal = Datatype('Animal')
    Animal.declare('dog')
    Animal.declare('horse')
    Animal.declare('cat')
    Animal.declare('bird')
    Animal.declare('fish')
    Animal = Animal.create()
    
    # Create the name, flower, animal variables for houses 1 to 5
    n = [Const('n%d' % i, Name) for i in range(1,6)]
    f = [Const('f%d' % i, Flower) for i in range(1,6)]
    a = [Const('a%d' % i, Animal) for i in range(1,6)]
    
    s = Solver()
    
    # All attributes must be unique
    s.add(Distinct(n))
    s.add(Distinct(f))
    s.add(Distinct(a))
    
    # Clue 1: Alice is in the second house.
    s.add(n[1] == Name.Alice)  # house2 is index 1 (0-indexed)
    
    # Clue 2: The person who loves lilies is the bird keeper.
    for i in range(5):
        s.add( (f[i] == Flower.lilies) == (a[i] == Animal.bird) )
    
    # Clue 3: Peter is somewhere to the right of the person who loves tulips.
    tulips_house = Int('tulips_house')
    s.add(tulips_house >= 1, tulips_house <= 5)
    for i in range(5):
        s.add(If(f[i] == Flower.tulips, tulips_house == i+1, True))
    peter_house = Int('peter_house')
    s.add(peter_house >= 1, peter_house <= 5)
    for i in range(5):
        s.add(If(n[i] == Name.Peter, peter_house == i+1, True))
    s.add(peter_house > tulips_house)
    
    # Clue 4: The fish enthusiast is the person who loves daffodils.
    for i in range(5):
        s.add( (a[i] == Animal.fish) == (f[i] == Flower.daffodils) )
    
    # Clue 5: The person who keeps horses is Eric.
    for i in range(5):
        s.add( (a[i] == Animal.horse) == (n[i] == Name.Eric) )
    
    # Clue 6: There are two houses between the dog owner and Bob.
    dog_house = Int('dog_house')
    s.add(dog_house >= 1, dog_house <= 5)
    for i in range(5):
        s.add(If(a[i] == Animal.dog, dog_house == i+1, True))
    bob_house = Int('bob_house')
    s.add(bob_house >= 1, bob_house <= 5)
    for i in range(5):
        s.add(If(n[i] == Name.Bob, bob_house == i+1, True))
    s.add(Or(dog_house == bob_house + 3, dog_house == bob_house - 3))
    
    # Clue 7: The fish enthusiast is directly left of Bob.
    fish_house = Int('fish_house')
    s.add(fish_house >= 1, fish_house <= 5)
    for i in range(5):
        s.add(If(a[i] == Animal.fish, fish_house == i+1, True))
    s.add(fish_house == bob_house - 1)
    
    # Clue 8: Alice is directly left of the person who keeps horses.
    s.add(a[2] == Animal.horse)  # house3 (index2) has the horse
    
    # Clue 9: The person who loves carnations is directly left of the person who loves tulips.
    carnations_house = Int('carnations_house')
    s.add(carnations_house >= 1, carnations_house <= 5)
    for i in range(5):
        s.add(If(f[i] == Flower.carnations, carnations_house == i+1, True))
    s.add(carnations_house == tulips_house - 1)
    
    # Clue 10: The cat lover is not in the first house.
    s.add(a[0] != Animal.cat)
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        # Dictionaries to map Z3 constants to strings
        name_dict = {
            Name.Alice: "Alice",
            Name.Eric: "Eric",
            Name.Arnold: "Arnold",
            Name.Bob: "Bob",
            Name.Peter: "Peter"
        }
        flower_dict = {
            Flower.tulips: "tulips",
            Flower.roses: "roses",
            Flower.lilies: "lilies",
            Flower.daffodils: "daffodils",
            Flower.carnations: "carnations"
        }
        animal_dict = {
            Animal.dog: "dog",
            Animal.horse: "horse",
            Animal.cat: "cat",
            Animal.bird: "bird",
            Animal.fish: "fish"
        }
        
        rows = []
        for i in range(5):
            house_num = str(i+1)
            name_val = model.eval(n[i])
            flower_val = model.eval(f[i])
            animal_val = model.eval(a[i])
            name_str = name_dict[name_val.as_long()]
            flower_str = flower_dict[flower_val.as_long()]
            animal_str = animal_dict[animal_val.as_long()]
            rows.append([house_num, name_str, flower_str, animal_str])
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Flower", "Animal"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()