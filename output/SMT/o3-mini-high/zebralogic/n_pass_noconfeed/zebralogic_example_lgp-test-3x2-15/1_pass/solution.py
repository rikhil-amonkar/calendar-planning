from z3 import *
import json

def main():
    s = Solver()

    # Person variables: represent the house number (1 to 3) of each person.
    Arnold = Int("Arnold")
    Peter = Int("Peter")
    Eric = Int("Eric")
    
    # Height variables: represent the house number (1 to 3) of the person with that height.
    short_h = Int("short_h")
    average_h = Int("average_h")
    very_short_h = Int("very_short_h")
    
    persons = [Arnold, Peter, Eric]
    heights = [short_h, average_h, very_short_h]
    
    # Domain constraints: each value is between 1 and 3.
    for var in persons:
        s.add(And(var >= 1, var <= 3))
    for var in heights:
        s.add(And(var >= 1, var <= 3))
    
    # Ensure all persons and heights are assigned to different houses.
    s.add(Distinct(Arnold, Peter, Eric))
    s.add(Distinct(short_h, average_h, very_short_h))
    
    # Clue 2: The person who is short is in the first house.
    s.add(short_h == 1)
    
    # Clue 3: There is one house between the person who is short and the person who is very short.
    s.add(Or(very_short_h - short_h == 2, short_h - very_short_h == 2))
    
    # Clue 4: Arnold and the person who is very short are next to each other.
    s.add(Or(Arnold - very_short_h == 1, very_short_h - Arnold == 1))
    
    # Clue 1: Peter is somewhere to the right of Eric.
    s.add(Peter > Eric)
    
    if s.check() == sat:
        m = s.model()
        
        # Build a mapping from house number to attributes.
        houses = {1: {"Name": None, "Height": None},
                  2: {"Name": None, "Height": None},
                  3: {"Name": None, "Height": None}}

        # Assign persons to houses.
        persons_dict = {
            "Arnold": m.evaluate(Arnold).as_long(),
            "Peter": m.evaluate(Peter).as_long(),
            "Eric": m.evaluate(Eric).as_long()
        }
        for name, house in persons_dict.items():
            houses[house]["Name"] = name

        # Assign heights to houses.
        heights_dict = {
            m.evaluate(short_h).as_long(): "short",
            m.evaluate(average_h).as_long(): "average",
            m.evaluate(very_short_h).as_long(): "very short"
        }
        for house, height in heights_dict.items():
            houses[house]["Height"] = height

        # Build the output dictionary in the required JSON format.
        output = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": []
            }
        }
        for house in sorted(houses.keys()):
            row = [str(house), houses[house]["Name"], houses[house]["Height"]]
            output["solution"]["rows"].append(row)
        
        print(json.dumps(output))
    else:
        print(json.dumps({"solution": {"header": ["House", "Name", "Height"], "rows": []}}))

if __name__ == "__main__":
    main()