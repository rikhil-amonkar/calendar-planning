import z3
import json

# Define EnumSorts for each attribute
name_sort, (Eric, Arnold) = z3.EnumSort('Name', ['Eric', 'Arnold'])
sport_sort, (basketball, soccer) = z3.EnumSort('Sport', ['basketball', 'soccer'])
hobby_sort, (photography, gardening) = z3.EnumSort('Hobby', ['photography', 'gardening'])

# Create variables for each house's attributes
name1, name2 = z3.Consts('name1 name2', name_sort)
sport1, sport2 = z3.Consts('sport1 sport2', sport_sort)
hobby1, hobby2 = z3.Consts('hobby1 hobby2', hobby_sort)

# Initialize solver
s = z3.Solver()

# Add constraints for uniqueness in each category
s.add(name1 != name2)
s.add(sport1 != sport2)
s.add(hobby1 != hobby2)

# Add constraints based on the clues
# Clue 1: If hobby is gardening, name is Arnold
s.add(z3.Implies(hobby1 == gardening, name1 == Arnold))
s.add(z3.Implies(hobby2 == gardening, name2 == Arnold))

# Clue 2: The photography enthusiast is not in the first house
s.add(hobby1 != photography)

# Clue 3: The person who loves soccer is not in the first house
s.add(sport1 != soccer)

# Check for solution
if s.check() == z3.sat:
    model = s.model()
    
    # Function to extract the value from the model
    def get_val(var):
        return model.eval(var).decl().name()
    
    # Extract values for each house
    h1_name = get_val(name1)
    h1_sport = get_val(sport1)
    h1_hobby = get_val(hobby1)
    
    h2_name = get_val(name2)
    h2_sport = get_val(sport2)
    h2_hobby = get_val(hobby2)
    
    # Construct the JSON solution
    solution = {
        "solution": {
            "header": ["House", "Name", "FavoriteSport", "Hobby"],
            "rows": [
                ["1", h1_name, h1_sport, h1_hobby],
                ["2", h2_name, h2_sport, h2_hobby]
            ]
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")