from z3 import *
import json

def main():
    solver = Solver()
    
    # Define integer variables for the house positions (1,2,3)
    house_peter = Int('house_peter')
    house_arnold = Int('house_arnold')
    house_eric   = Int('house_eric')
    
    house_doctor   = Int('house_doctor')
    house_teacher  = Int('house_teacher')
    house_engineer = Int('house_engineer')
    
    house_cooking     = Int('house_cooking')
    house_photography = Int('house_photography')
    house_gardening   = Int('house_gardening')
    
    # All variables must take a value between 1 and 3 (the three houses)
    all_vars = [house_peter, house_arnold, house_eric,
                house_doctor, house_teacher, house_engineer,
                house_cooking, house_photography, house_gardening]
    for var in all_vars:
        solver.add(var >= 1, var <= 3)
    
    # All names appear in distinct houses.
    solver.add(Distinct(house_peter, house_arnold, house_eric))
    # All occupations appear in distinct houses.
    solver.add(Distinct(house_doctor, house_teacher, house_engineer))
    # All hobbies appear in distinct houses.
    solver.add(Distinct(house_cooking, house_photography, house_gardening))
    
    # Clue 1: The person who is a doctor and Eric are next to each other.
    solver.add(Abs(house_doctor - house_eric) == 1)
    
    # Clue 2: The person who loves cooking is directly left of the person who is a teacher.
    solver.add(house_cooking + 1 == house_teacher)
    
    # Clue 3: The person who is a doctor is somewhere to the right of the person who enjoys gardening.
    solver.add(house_doctor > house_gardening)
    
    # Clue 4: The photography enthusiast is the person who is a teacher.
    solver.add(house_photography == house_teacher)
    
    # Clue 5: The person who is an engineer is Peter.
    solver.add(house_engineer == house_peter)
    
    if solver.check() == sat:
        model = solver.model()
        
        # Build the results for houses 1, 2, and 3.
        rows = []
        for house in range(1, 4):
            # Determine the Name
            if model.evaluate(house_peter).as_long() == house:
                name = "Peter"
            elif model.evaluate(house_arnold).as_long() == house:
                name = "Arnold"
            elif model.evaluate(house_eric).as_long() == house:
                name = "Eric"
            
            # Determine the Occupation
            if model.evaluate(house_doctor).as_long() == house:
                occupation = "doctor"
            elif model.evaluate(house_teacher).as_long() == house:
                occupation = "teacher"
            elif model.evaluate(house_engineer).as_long() == house:
                occupation = "engineer"
            
            # Determine the Hobby
            if model.evaluate(house_cooking).as_long() == house:
                hobby = "cooking"
            elif model.evaluate(house_photography).as_long() == house:
                hobby = "photography"
            elif model.evaluate(house_gardening).as_long() == house:
                hobby = "gardening"
            
            rows.append([str(house), name, occupation, hobby])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Occupation", "Hobby"],
                "rows": rows
            }
        }
        # Print the solution as formatted JSON.
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()