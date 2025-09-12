import json
from z3 import *

def main():
    # Initialize the solver
    solver = Solver()
    
    # Define variables for each attribute's house assignment
    Arnold_house = Int('Arnold_house')
    Peter_house = Int('Peter_house')
    Eric_house = Int('Eric_house')
    
    doctor_house = Int('doctor_house')
    teacher_house = Int('teacher_house')
    engineer_house = Int('engineer_house')
    
    associate_house = Int('associate_house')
    high_school_house = Int('high_school_house')
    bachelor_house = Int('bachelor_house')
    
    desert_smoothie_house = Int('desert_smoothie_house')
    cherry_smoothie_house = Int('cherry_smoothie_house')
    watermelon_smoothie_house = Int('watermelon_smoothie_house')
    
    gardening_house = Int('gardening_house')
    cooking_house = Int('cooking_house')
    photography_house = Int('photography_house')
    
    # All houses must be between 1 and 3
    houses = [1, 2, 3]
    attributes = [
        [Arnold_house, Peter_house, Eric_house],
        [doctor_house, teacher_house, engineer_house],
        [associate_house, high_school_house, bachelor_house],
        [desert_smoothie_house, cherry_smoothie_house, watermelon_smoothie_house],
        [gardening_house, cooking_house, photography_house]
    ]
    
    for attr_group in attributes:
        for var in attr_group:
            solver.add(And(var >= 1, var <= 3))
        solver.add(Distinct(attr_group))
    
    # Add clue constraints
    # 1. The Desert smoothie lover is the person who is a doctor.
    solver.add(desert_smoothie_house == doctor_house)
    
    # 2. Arnold is not in the third house.
    solver.add(Arnold_house != 3)
    
    # 3. The person who likes Cherry smoothies is somewhere to the right of Peter.
    solver.add(cherry_smoothie_house > Peter_house)
    
    # 4. The person who loves cooking is in the second house.
    solver.add(cooking_house == 2)
    
    # 5. The person who loves cooking is Peter.
    solver.add(cooking_house == Peter_house)
    
    # 6. The person with an associate's degree is somewhere to the right of the person who enjoys gardening.
    solver.add(associate_house > gardening_house)
    
    # 7. The person with a bachelor's degree is somewhere to the right of the Desert smoothie lover.
    solver.add(bachelor_house > desert_smoothie_house)
    
    # 8. The person who loves cooking is the person who is a doctor.
    solver.add(cooking_house == doctor_house)
    
    # 9. The photography enthusiast is the person who is a teacher.
    solver.add(photography_house == teacher_house)
    
    # Check satisfiability
    if solver.check() == sat:
        model = solver.model()
        
        # Build reverse mapping from house number to attribute values
        solution = {house: {} for house in houses}
        attr_groups = [
            ('Name', {'Arnold': Arnold_house, 'Peter': Peter_house, 'Eric': Eric_house}),
            ('Occupation', {'doctor': doctor_house, 'teacher': teacher_house, 'engineer': engineer_house}),
            ('Education', {'associate': associate_house, 'high school': high_school_house, 'bachelor': bachelor_house}),
            ('Smoothie', {'desert': desert_smoothie_house, 'cherry': cherry_smoothie_house, 'watermelon': watermelon_smoothie_house}),
            ('Hobby', {'gardening': gardening_house, 'cooking': cooking_house, 'photography': photography_house})
        ]
        
        for attr_name, attr_dict in attr_groups:
            for value, var in attr_dict.items():
                house_num = model.eval(var).as_long()
                solution[house_num][attr_name] = value
        
        # Prepare JSON output
        header = ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"]
        rows = []
        for house in sorted(solution.keys()):
            data = solution[house]
            row = [
                str(house),
                data['Name'],
                data['Occupation'],
                data['Education'],
                data['Smoothie'],
                data['Hobby']
            ]
            rows.append(row)
        
        output = {"solution": {"header": header, "rows": rows}}
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()