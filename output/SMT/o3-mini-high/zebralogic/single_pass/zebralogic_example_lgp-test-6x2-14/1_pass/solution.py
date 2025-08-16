from z3 import *
import json

def main():
    # Define person variables (each represents the house number 1..6)
    Peter   = Int("Peter")
    Arnold  = Int("Arnold")
    Bob     = Int("Bob")
    Carol   = Int("Carol")
    Eric    = Int("Eric")
    Alice   = Int("Alice")
    persons = {"Peter": Peter, "Arnold": Arnold, "Bob": Bob, "Carol": Carol, "Eric": Eric, "Alice": Alice}

    # Define cigar variables (each represents the house number 1..6)
    blends         = Int("blends")
    yellow_monster = Int("yellow_monster")
    pall_mall      = Int("pall_mall")
    blue_master    = Int("blue_master")
    dunhill        = Int("dunhill")
    prince         = Int("prince")
    cigars = {
        "blends": blends,
        "yellow monster": yellow_monster,
        "pall mall": pall_mall,
        "blue master": blue_master,
        "dunhill": dunhill,
        "prince": prince
    }

    s = Solver()

    # Set domains and ensure all persons have distinct houses.
    for p in persons.values():
        s.add(p >= 1, p <= 6)
    s.add(Distinct(list(persons.values())))

    # Set domains and ensure all cigars are in distinct houses.
    for c in cigars.values():
        s.add(c >= 1, c <= 6)
    s.add(Distinct(list(cigars.values())))

    # Clue 8: Peter is in the first house.
    s.add(Peter == 1)
    # Clue 9: Bob is in the third house.
    s.add(Bob == 3)
    # Clue 6: Eric is in the sixth house.
    s.add(Eric == 6)
    # Clue 7: Carol and Eric are next to each other.
    s.add(Or(Carol - Eric == 1, Eric - Carol == 1))
    
    # From the distinct houses, with Peter, Bob, Eric fixed and Carol next to Eric,
    # Carol must be in house 5. (The only possibility when Eric is 6)
    # The remaining persons, Arnold and Alice, will then automatically take houses 2 and 4.
    
    # Clue 2: The person who smokes Blue Master is in the fifth house.
    s.add(blue_master == 5)
    # Clue 5: The person partial to Pall Mall is in the third house.
    s.add(pall_mall == 3)
    
    # Clue 1: Arnold is somewhere to the left of the person who smokes "blends".
    s.add(Arnold < blends)
    # Clue 3: Arnold is somewhere to the left of the person who smokes "prince".
    s.add(Arnold < prince)
    # Clue 4: There is one house between the person who smokes "yellow monster" and the person who smokes "blends".
    s.add(Abs(yellow_monster - blends) == 2)

    if s.check() == sat:
        m = s.model()
        # Build a mapping from house to person.
        house_to_person = {}
        for name, var in persons.items():
            house_number = m[var].as_long()
            house_to_person[house_number] = name

        # Build a mapping from house to cigar.
        house_to_cigar = {}
        for cigar_name, var in cigars.items():
            house_number = m[var].as_long()
            house_to_cigar[house_number] = cigar_name

        # Create result rows in order of houses 1 to 6.
        rows = []
        for house in range(1, 7):
            # Each row: House number (as string), Name, Cigar.
            rows.append([str(house), house_to_person[house], house_to_cigar[house]])

        result = {
            "solution": {
                "header": ["House", "Name", "Cigar"],
                "rows": rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()