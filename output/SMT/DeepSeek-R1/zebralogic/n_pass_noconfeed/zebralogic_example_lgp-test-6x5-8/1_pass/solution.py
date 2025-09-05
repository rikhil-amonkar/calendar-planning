import json
from z3 import *

def main():
    # Create the solver
    solver = Solver()

    # Define the attributes using EnumSort
    Name, (Arnold, Peter, Bob, Eric, Carol, Alice) = EnumSort('Name', ['Arnold', 'Peter', 'Bob', 'Eric', 'Carol', 'Alice'])
    Animal, (horse, rabbit, fish, cat, bird, dog) = EnumSort('Animal', ['horse', 'rabbit', 'fish', 'cat', 'bird', 'dog'])
    Occupation, (engineer, nurse, lawyer, teacher, artist, doctor) = EnumSort('Occupation', ['engineer', 'nurse', 'lawyer', 'teacher', 'artist', 'doctor'])
    FavoriteSport, (basketball, volleyball, soccer, tennis, baseball, swimming) = EnumSort('FavoriteSport', ['basketball', 'volleyball', 'soccer', 'tennis', 'baseball', 'swimming'])
    Height, (average, tall, short, very_short, very_tall, super_tall) = EnumSort('Height', ['average', 'tall', 'short', 'very short', 'very tall', 'super tall'])

    # Create arrays for each attribute for the 6 houses
    names = [Const(f'name_{i}', Name) for i in range(6)]
    animals = [Const(f'animal_{i}', Animal) for i in range(6)]
    occupations = [Const(f'occupation_{i}', Occupation) for i in range(6)]
    sports = [Const(f'sport_{i}', FavoriteSport) for i in range(6)]
    heights = [Const(f'height_{i}', Height) for i in range(6)]

    # Each attribute must be unique per house
    solver.add(Distinct(names))
    solver.add(Distinct(animals))
    solver.add(Distinct(occupations))
    solver.add(Distinct(sports))
    solver.add(Distinct(heights))

    # Add constraints from the clues
    # 1. The person who is an engineer is the dog owner.
    for i in range(6):
        solver.add(Implies(occupations[i] == engineer, animals[i] == dog))

    # 2. The person who has an average height is somewhere to the left of the person who is short.
    avg_index = Int('avg_index')
    short_index = Int('short_index')
    solver.add(Exists([avg_index, short_index], And(
        And([If(heights[i] == average, avg_index == i, True) for i in range(6)]),
        And([If(heights[i] == short, short_index == i, True) for i in range(6)]),
        avg_index < short_index
    )))

    # 3. The person who has an average height is directly left of the rabbit owner.
    for i in range(5):
        solver.add(Implies(heights[i] == average, And(animals[i+1] == rabbit, heights[i+1] != average)))

    # 4. The person who is tall is somewhere to the left of the person who is very short.
    tall_index = Int('tall_index')
    very_short_index = Int('very_short_index')
    solver.add(Exists([tall_index, very_short_index], And(
        And([If(heights[i] == tall, tall_index == i, True) for i in range(6)]),
        And([If(heights[i] == very_short, very_short_index == i, True) for i in range(6)]),
        tall_index < very_short_index
    )))

    # 5. Arnold is the cat lover.
    for i in range(6):
        solver.add(Implies(names[i] == Arnold, animals[i] == cat))

    # 6. The person who keeps horses is the person who is a teacher.
    for i in range(6):
        solver.add(Implies(animals[i] == horse, occupations[i] == teacher))

    # 7. Carol is the person who loves soccer.
    for i in range(6):
        solver.add(Implies(names[i] == Carol, sports[i] == soccer))

    # 8. The person who is tall is the person who loves volleyball.
    for i in range(6):
        solver.add(Implies(heights[i] == tall, sports[i] == volleyball))

    # 9. The person who is a lawyer is in the fifth house.
    solver.add(occupations[4] == lawyer)

    # 10. The person who loves tennis is the person who is a teacher.
    for i in range(6):
        solver.add(Implies(sports[i] == tennis, occupations[i] == teacher))

    # 11. The person who has an average height is the person who loves swimming.
    for i in range(6):
        solver.add(Implies(heights[i] == average, sports[i] == swimming))

    # 12. The person who loves baseball is directly left of the person who is an engineer.
    for i in range(5):
        solver.add(Implies(sports[i] == baseball, occupations[i+1] == engineer))

    # 13. Peter is the person who is a nurse.
    for i in range(6):
        solver.add(Implies(names[i] == Peter, occupations[i] == nurse))

    # 14. Bob is somewhere to the right of the person who is an artist.
    bob_index = Int('bob_index')
    artist_index = Int('artist_index')
    solver.add(Exists([bob_index, artist_index], And(
        And([If(names[i] == Bob, bob_index == i, True) for i in range(6)]),
        And([If(occupations[i] == artist, artist_index == i, True) for i in range(6)]),
        bob_index > artist_index
    )))

    # 15. The person who is a teacher is directly left of the person who loves soccer.
    for i in range(5):
        solver.add(Implies(occupations[i] == teacher, sports[i+1] == soccer))

    # 16. The rabbit owner is Alice.
    for i in range(6):
        solver.add(Implies(animals[i] == rabbit, names[i] == Alice))

    # 17. The fish enthusiast is Carol.
    for i in range(6):
        solver.add(Implies(animals[i] == fish, names[i] == Carol))

    # 18. The person who loves baseball is in the first house.
    solver.add(sports[0] == baseball)

    # 19. The cat lover is somewhere to the right of the person who is very short.
    cat_index = Int('cat_index')
    very_short_index2 = Int('very_short_index2')
    solver.add(Exists([cat_index, very_short_index2], And(
        And([If(animals[i] == cat, cat_index == i, True) for i in range(6)]),
        And([If(heights[i] == very_short, very_short_index2 == i, True) for i in range(6)]),
        cat_index > very_short_index2
    )))

    # 20. The person who is super tall is in the fifth house.
    solver.add(heights[4] == super_tall)

    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare the result table
        header = ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"]
        rows = []
        
        # Function to get the string value from the model evaluation
        def get_value(model, var, sort_values):
            for name, value in sort_values:
                if model.eval(var) == value:
                    return name
            return None
        
        # Mapping for each sort to string names
        name_map = [('Arnold', Arnold), ('Peter', Peter), ('Bob', Bob), ('Eric', Eric), ('Carol', Carol), ('Alice', Alice)]
        animal_map = [('horse', horse), ('rabbit', rabbit), ('fish', fish), ('cat', cat), ('bird', bird), ('dog', dog)]
        occupation_map = [('engineer', engineer), ('nurse', nurse), ('lawyer', lawyer), ('teacher', teacher), ('artist', artist), ('doctor', doctor)]
        sport_map = [('basketball', basketball), ('volleyball', volleyball), ('soccer', soccer), ('tennis', tennis), ('baseball', baseball), ('swimming', swimming)]
        height_map = [('average', average), ('tall', tall), ('short', short), ('very short', very_short), ('very tall', very_tall), ('super tall', super_tall)]
        
        for i in range(6):
            house_num = str(i+1)
            n_val = get_value(model, names[i], name_map)
            a_val = get_value(model, animals[i], animal_map)
            o_val = get_value(model, occupations[i], occupation_map)
            s_val = get_value(model, sports[i], sport_map)
            h_val = get_value(model, heights[i], height_map)
            rows.append([house_num, n_val, a_val, o_val, s_val, h_val])
        
        # Create the solution dictionary
        solution_dict = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        
        # Output as JSON
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()