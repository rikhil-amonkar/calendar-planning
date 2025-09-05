from z3 import *
import json

def main():
    solver = Solver()
    
    # Create variables for each attribute. They represent the house number (1 to 5).
    names = {
        "Eric": Int("Eric"),
        "Peter": Int("Peter"),
        "Alice": Int("Alice"),
        "Bob": Int("Bob"),
        "Arnold": Int("Arnold")
    }
    
    nationals = {
        "norwegian": Int("norwegian"),
        "brit": Int("brit"),
        "swede": Int("swede"),
        "dane": Int("dane"),
        "german": Int("german")
    }
    
    vacations = {
        "cruise": Int("cruise"),
        "mountain": Int("mountain"),
        "camping": Int("camping"),
        "beach": Int("beach"),
        "city": Int("city")
    }
    
    # Use "high_school" as key for education, but output as "high school"
    education = {
        "bachelor": Int("bachelor"),
        "master": Int("master"),
        "associate": Int("associate"),
        "doctorate": Int("doctorate"),
        "high_school": Int("high_school")
    }
    
    occupations = {
        "artist": Int("artist"),
        "doctor": Int("doctor"),
        "engineer": Int("engineer"),
        "teacher": Int("teacher"),
        "lawyer": Int("lawyer")
    }
    
    # List of all variables by category for domain and distinct constraints
    all_vars = list(names.values()) + list(nationals.values()) + list(vacations.values()) + list(education.values()) + list(occupations.values())
    
    # Domain constraints: each variable is in the range 1..5
    for var in all_vars:
        solver.add(var >= 1, var <= 5)
    
    # Add distinct constraints for each category
    solver.add(Distinct(list(names.values())))
    solver.add(Distinct(list(nationals.values())))
    solver.add(Distinct(list(vacations.values())))
    solver.add(Distinct(list(education.values())))
    solver.add(Distinct(list(occupations.values())))
    
    # Puzzle Clues translated into constraints:
    # 1. The person who likes going on cruises is the person who is a lawyer.
    solver.add(vacations["cruise"] == occupations["lawyer"])
    
    # 2. The person who loves beach vacations is directly left of Arnold.
    solver.add(vacations["beach"] + 1 == names["Arnold"])
    
    # 3. The person with a doctorate is somewhere to the left of Bob.
    solver.add(education["doctorate"] < names["Bob"])
    
    # 4. The person with an associate's degree is the person who likes going on cruises.
    solver.add(education["associate"] == vacations["cruise"])
    
    # 5. Peter is not in the first house.
    solver.add(names["Peter"] != 1)
    
    # 6. The person who is an artist is Peter.
    solver.add(occupations["artist"] == names["Peter"])
    
    # 7. The person who enjoys camping trips is the person with a master's degree.
    solver.add(vacations["camping"] == education["master"])
    
    # 8. The Dane is somewhere to the right of the person who is a doctor.
    solver.add(nationals["dane"] > occupations["doctor"])
    
    # 9. The person with an associate's degree is directly left of the person who is an engineer.
    solver.add(education["associate"] + 1 == occupations["engineer"])
    
    # 10. The person who enjoys camping trips is the British person.
    solver.add(vacations["camping"] == nationals["brit"])
    
    # 11. The Norwegian and the person with a bachelor's degree are next to each other.
    solver.add(Or(nationals["norwegian"] - education["bachelor"] == 1, education["bachelor"] - nationals["norwegian"] == 1))
    
    # 12. The person who is an artist is the Swedish person.
    solver.add(names["Peter"] == nationals["swede"])
    
    # 13. Bob is not in the fourth house.
    solver.add(names["Bob"] != 4)
    
    # 14. The person who enjoys camping trips is Eric.
    solver.add(vacations["camping"] == names["Eric"])
    
    # 15. Alice is the German.
    solver.add(names["Alice"] == nationals["german"])
    
    # 16. The person who loves beach vacations is somewhere to the left of the person who prefers city breaks.
    solver.add(vacations["beach"] < vacations["city"])
    
    # 17. The person who enjoys mountain retreats is in the fifth house.
    solver.add(vacations["mountain"] == 5)
    
    # 18. The person who likes going on cruises is somewhere to the right of the person who loves beach vacations.
    solver.add(vacations["cruise"] > vacations["beach"])
    
    # 19. The person with a bachelor's degree is in the third house.
    solver.add(education["bachelor"] == 3)
    
    # Solve the puzzle
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare inverse mapping: for each house (1 to 5), determine the attribute values.
        house_info = {}
        # Helper function to retrieve which key in the mapping has the given house number.
        def get_item(mapping, house_num):
            for key, var in mapping.items():
                if model.evaluate(var).as_long() == house_num:
                    # For education, convert key "high_school" to "high school"
                    if key == "high_school":
                        return "high school"
                    return key
            return None

        rows = []
        # Houses are numbered 1 to 5 (1 is left-most)
        for house in range(1, 6):
            row = [
                str(house),
                get_item(names, house),
                get_item(nationals, house),
                get_item(vacations, house),
                get_item(education, house),
                get_item(occupations, house)
            ]
            rows.append(row)
        
        # Build JSON structure with the required format
        solution_json = {
            "solution": {
                "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
                "rows": rows
            }
        }
        print(json.dumps(solution_json, indent=2))
    else:
        print(json.dumps({"solution": "No solution found."}))

if __name__ == '__main__':
    main()