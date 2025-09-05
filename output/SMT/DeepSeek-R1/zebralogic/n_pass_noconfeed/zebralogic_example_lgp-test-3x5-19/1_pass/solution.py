import z3
import json

def main():
    solver = z3.Solver()
    
    # Define the possible values for each category
    names = ['Arnold', 'Peter', 'Eric']
    occupations = ['doctor', 'teacher', 'engineer']
    educations = ['associate', 'high school', 'bachelor']
    smoothies = ['desert', 'cherry', 'watermelon']
    hobbies = ['gardening', 'cooking', 'photography']
    
    # Create variables for each attribute's house assignment
    Arnold_house = z3.Int('Arnold_house')
    Peter_house = z3.Int('Peter_house')
    Eric_house = z3.Int('Eric_house')
    
    doctor_house = z3.Int('doctor_house')
    teacher_house = z3.Int('teacher_house')
    engineer_house = z3.Int('engineer_house')
    
    associate_house = z3.Int('associate_house')
    high_school_house = z3.Int('high_school_house')
    bachelor_house = z3.Int('bachelor_house')
    
    desert_house = z3.Int('desert_house')
    cherry_house = z3.Int('cherry_house')
    watermelon_house = z3.Int('watermelon_house')
    
    gardening_house = z3.Int('gardening_house')
    cooking_house = z3.Int('cooking_house')
    photography_house = z3.Int('photography_house')
    
    # All houses must be between 1 and 3
    houses = [1, 2, 3]
    for var in [Arnold_house, Peter_house, Eric_house, doctor_house, teacher_house, engineer_house,
                associate_house, high_school_house, bachelor_house, desert_house, cherry_house, watermelon_house,
                gardening_house, cooking_house, photography_house]:
        solver.add(z3.And(var >= 1, var <= 3))
    
    # Each set of attributes must have distinct houses
    solver.add(z3.Distinct([Arnold_house, Peter_house, Eric_house]))
    solver.add(z3.Distinct([doctor_house, teacher_house, engineer_house]))
    solver.add(z3.Distinct([associate_house, high_school_house, bachelor_house]))
    solver.add(z3.Distinct([desert_house, cherry_house, watermelon_house]))
    solver.add(z3.Distinct([gardening_house, cooking_house, photography_house]))
    
    # Add clues
    solver.add(desert_house == doctor_house)  # Clue 1
    solver.add(Arnold_house != 3)             # Clue 2
    solver.add(cherry_house > Peter_house)    # Clue 3
    solver.add(cooking_house == 2)            # Clue 4
    solver.add(cooking_house == Peter_house)  # Clue 5
    solver.add(associate_house > gardening_house)  # Clue 6
    solver.add(bachelor_house > desert_house) # Clue 7
    solver.add(cooking_house == doctor_house) # Clue 8
    solver.add(photography_house == teacher_house)  # Clue 9
    
    # Check if satisfiable
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Create a mapping from house number to attributes
        result = {house: {'Name': None, 'Occupation': None, 'Education': None, 'Smoothie': None, 'Hobby': None} for house in houses}
        
        # Helper function to assign value to house based on model
        def assign_value(house_var, value, category):
            house_num = model[house_var].as_long()
            result[house_num][category] = value
        
        # Assign names
        assign_value(Arnold_house, 'Arnold', 'Name')
        assign_value(Peter_house, 'Peter', 'Name')
        assign_value(Eric_house, 'Eric', 'Name')
        
        # Assign occupations
        assign_value(doctor_house, 'doctor', 'Occupation')
        assign_value(teacher_house, 'teacher', 'Occupation')
        assign_value(engineer_house, 'engineer', 'Occupation')
        
        # Assign educations
        assign_value(associate_house, 'associate', 'Education')
        assign_value(high_school_house, 'high school', 'Education')
        assign_value(bachelor_house, 'bachelor', 'Education')
        
        # Assign smoothies
        assign_value(desert_house, 'desert', 'Smoothie')
        assign_value(cherry_house, 'cherry', 'Smoothie')
        assign_value(watermelon_house, 'watermelon', 'Smoothie')
        
        # Assign hobbies
        assign_value(gardening_house, 'gardening', 'Hobby')
        assign_value(cooking_house, 'cooking', 'Hobby')
        assign_value(photography_house, 'photography', 'Hobby')
        
        # Prepare output in required JSON format
        rows = []
        for house in houses:
            attr = result[house]
            rows.append([
                str(house),
                attr['Name'],
                attr['Occupation'],
                attr['Education'],
                attr['Smoothie'],
                attr['Hobby']
            ])
        
        output = {
            "solution": {
                "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
                "rows": rows
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()