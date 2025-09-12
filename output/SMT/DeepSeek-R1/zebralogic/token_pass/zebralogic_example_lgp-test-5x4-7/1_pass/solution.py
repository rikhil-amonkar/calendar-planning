import json
from z3 import *

def main():
    # Define the attributes using EnumSort
    Name, (Alice, Peter, Bob, Eric, Arnold) = EnumSort('Name', ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold'])
    Smoothie, (Lime, Dragonfruit, Desert, Watermelon, Cherry) = EnumSort('Smoothie', ['Lime', 'Dragonfruit', 'Desert', 'Watermelon', 'Cherry'])
    Animal, (Horse, Dog, Bird, Fish, Cat) = EnumSort('Animal', ['Horse', 'Dog', 'Bird', 'Fish', 'Cat'])
    Nationality, (German, Swede, Norwegian, Brit, Dane) = EnumSort('Nationality', ['German', 'Swede', 'Norwegian', 'Brit', 'Dane'])
    
    # Create variables for each house (index 0 to 4 for houses 1 to 5)
    names = [Const(f'name_{i}', Name) for i in range(5)]
    smoothies = [Const(f'smoothie_{i}', Smoothie) for i in range(5)]
    animals = [Const(f'animal_{i}', Animal) for i in range(5)]
    nationalities = [Const(f'nationality_{i}', Nationality) for i in range(5)]
    
    s = Solver()
    
    # All attributes must be distinct
    s.add(Distinct(names))
    s.add(Distinct(smoothies))
    s.add(Distinct(animals))
    s.add(Distinct(nationalities))
    
    # Clue 1: The Swedish person is directly left of the dog owner.
    for i in range(4):
        s.add(Implies(nationalities[i] == Swede, animals[i+1] == Dog))
    
    # Clue 2: There are two houses between the dog owner and the British person.
    dog_house = Int('dog_house')
    brit_house = Int('brit_house')
    for i in range(5):
        s.add(If(animals[i] == Dog, dog_house == i+1, True))
        s.add(If(nationalities[i] == Brit, brit_house == i+1, True))
    s.add(Or(dog_house - brit_house == 3, brit_house - dog_house == 3))
    
    # Clue 3: The Dane is the person who keeps horses.
    for i in range(5):
        s.add(Implies(nationalities[i] == Dane, animals[i] == Horse))
    
    # Clue 4: The bird keeper is somewhere to the right of the cat lover.
    cat_house = Int('cat_house')
    bird_house = Int('bird_house')
    for i in range(5):
        s.add(If(animals[i] == Cat, cat_house == i+1, True))
        s.add(If(animals[i] == Bird, bird_house == i+1, True))
    s.add(bird_house > cat_house)
    
    # Clue 5: The dog owner is directly left of the person who drinks Lime smoothies.
    for i in range(4):
        s.add(Implies(animals[i] == Dog, smoothies[i+1] == Lime))
    
    # Clue 6: Eric is the cat lover.
    for i in range(5):
        s.add(Implies(names[i] == Eric, animals[i] == Cat))
    
    # Clue 7: Bob is the bird keeper.
    for i in range(5):
        s.add(Implies(names[i] == Bob, animals[i] == Bird))
    
    # Clue 8: The person who likes Cherry smoothies is directly left of Peter.
    for i in range(4):
        s.add(Implies(smoothies[i] == Cherry, names[i+1] == Peter))
    
    # Clue 9: The bird keeper is the Watermelon smoothie lover.
    for i in range(5):
        s.add(Implies(animals[i] == Bird, smoothies[i] == Watermelon))
    
    # Clue 10: The Desert smoothie lover is the dog owner.
    for i in range(5):
        s.add(Implies(smoothies[i] == Desert, animals[i] == Dog))
    
    # Clue 11: The person who keeps horses is in the third house.
    s.add(animals[2] == Horse)
    
    # Clue 12: The Norwegian is Alice.
    for i in range(5):
        s.add(Implies(nationalities[i] == Norwegian, names[i] == Alice))
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        result = []
        for i in range(5):
            name_val = m.eval(names[i])
            smoothie_val = m.eval(smoothies[i])
            animal_val = m.eval(animals[i])
            nationality_val = m.eval(nationalities[i])
            
            # Convert Z3 values to strings
            name_str = name_val.decl().name()
            smoothie_str = smoothie_val.decl().name()
            animal_str = animal_val.decl().name()
            nationality_str = nationality_val.decl().name()
            
            result.append([str(i+1), name_str, smoothie_str, animal_str, nationality_str])
        
        # Format the output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()