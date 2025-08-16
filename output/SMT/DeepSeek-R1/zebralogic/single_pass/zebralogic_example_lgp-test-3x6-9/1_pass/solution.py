import z3
import json

def main():
    # Define the attributes and their possible values
    attributes_list = ['Name', 'CarModel', 'HouseStyle', 'Pet', 'Occupation', 'Vacation']
    value_maps = {
        'Name': ['Peter', 'Arnold', 'Eric'],
        'CarModel': ['toyota camry', 'ford f150', 'tesla model 3'],
        'HouseStyle': ['ranch', 'colonial', 'victorian'],
        'Pet': ['cat', 'dog', 'fish'],
        'Occupation': ['engineer', 'doctor', 'teacher'],
        'Vacation': ['city', 'mountain', 'beach']
    }
    
    # Create Z3 variables for each attribute in each house (houses 1,2,3 -> indices 0,1,2)
    V = {}
    for attr in attributes_list:
        V[attr] = [z3.Int(f"{attr}_{i}") for i in range(1,4)]
    
    # Initialize solver
    s = z3.Solver()
    
    # Add constraints: each attribute's values are distinct and in the range [0, 2]
    for attr in attributes_list:
        s.add(z3.Distinct(V[attr][0], V[attr][1], V[attr][2]))
        for i in range(3):
            s.add(V[attr][i] >= 0, V[attr][i] < 3)
    
    # Clue 1: The person with an aquarium of fish is in the first house.
    s.add(V['Pet'][0] == 2)  # 'fish' is at index 2
    
    # Clue 2: The person who owns a Toyota Camry is in the second house.
    s.add(V['CarModel'][1] == 0)  # 'toyota camry' is at index 0
    
    # Clue 3: The person who enjoys mountain retreats is not in the second house.
    s.add(V['Vacation'][1] != 1)  # 'mountain' is at index 1
    
    # Clue 4: The person who prefers city breaks is not in the second house.
    s.add(V['Vacation'][1] != 0)  # 'city' is at index 0
    
    # Clue 5: The person in a ranch-style home is somewhere to the left of Peter.
    # ranch index: 0, Peter index: 0
    s.add(z3.Or(
        z3.And(V['HouseStyle'][0] == 0, V['Name'][1] == 0),
        z3.And(V['HouseStyle'][0] == 0, V['Name'][2] == 0),
        z3.And(V['HouseStyle'][1] == 0, V['Name'][2] == 0)
    ))
    
    # Clue 6: The person who owns a Toyota Camry is directly left of the person living in a colonial-style house.
    # Toyota Camry is at house2 (index1), so colonial must be at house3 (index2). Colonial index: 1
    s.add(V['HouseStyle'][2] == 1)
    
    # Clue 7: Arnold is the person who has a cat.
    # Arnold index: 1, cat index: 0
    s.add(z3.Or(
        z3.And(V['Name'][0] == 1, V['Pet'][0] == 0),
        z3.And(V['Name'][1] == 1, V['Pet'][1] == 0),
        z3.And(V['Name'][2] == 1, V['Pet'][2] == 0)
    ))
    
    # Clue 8: Eric is somewhere to the left of the person who enjoys mountain retreats.
    # Eric index: 2, mountain index: 1
    s.add(z3.Or(
        z3.And(V['Name'][0] == 2, V['Vacation'][1] == 1),
        z3.And(V['Name'][0] == 2, V['Vacation'][2] == 1),
        z3.And(V['Name'][1] == 2, V['Vacation'][2] == 1)
    ))
    
    # Clue 9: The person who is an engineer is not in the third house.
    s.add(V['Occupation'][2] != 0)  # engineer index: 0
    
    # Clue 10: The person who owns a Tesla Model 3 is somewhere to the left of the person who is a teacher.
    # Tesla index: 2, teacher index: 2
    s.add(z3.Or(
        z3.And(V['CarModel'][0] == 2, V['Occupation'][1] == 2),
        z3.And(V['CarModel'][0] == 2, V['Occupation'][2] == 2),
        z3.And(V['CarModel'][1] == 2, V['Occupation'][2] == 2)
    ))
    
    # Clue 11: The person who owns a dog is the person who is an engineer.
    # dog index: 1, engineer index: 0
    s.add(z3.Or(
        z3.And(V['Pet'][0] == 1, V['Occupation'][0] == 0),
        z3.And(V['Pet'][1] == 1, V['Occupation'][1] == 0),
        z3.And(V['Pet'][2] == 1, V['Occupation'][2] == 0)
    ))
    
    # Check for a solution
    if s.check() == z3.sat:
        m = s.model()
        rows = []
        for house_index in range(3):
            row = [str(house_index + 1)]
            for attr in attributes_list:
                var = V[attr][house_index]
                val = m[var]
                if val is not None:
                    idx = val.as_long()
                    row.append(value_maps[attr][idx])
                else:
                    row.append(None)  # Should not happen if model is complete
            rows.append(row)
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()