from z3 import *
import json

def main():
    solver = Solver()
    houses = range(5)  # Houses indexed 0..4 correspond to houses 1..5

    # Define integer variables for each house: name, smoothie, nationality.
    # Domain: 0..4
    names = [Int(f"name_{i}") for i in houses]
    smoothies = [Int(f"smoothie_{i}") for i in houses]
    nats = [Int(f"nat_{i}") for i in houses]

    for i in houses:
        solver.add(And(names[i] >= 0, names[i] < 5))
        solver.add(And(smoothies[i] >= 0, smoothies[i] < 5))
        solver.add(And(nats[i] >= 0, nats[i] < 5))

    # All attributes must be distinct across houses.
    solver.add(Distinct(names))
    solver.add(Distinct(smoothies))
    solver.add(Distinct(nats))

    # Mappings:
    # Names: Arnold=0, Eric=1, Bob=2, Peter=3, Alice=4
    # Smoothies: desert=0, watermelon=1, lime=2, cherry=3, dragonfruit=4
    # Nationalities: german=0, swede=1, norwegian=2, dane=3, brit=4

    # Clue 2: The Dragonfruit smoothie lover is in the second house (index 1).
    solver.add(smoothies[1] == 4)
    # Clue 11: The Watermelon smoothie lover is in the third house (index 2).
    solver.add(smoothies[2] == 1)
    # Clue 10: Alice is in the third house (index 2, and Alice=4).
    solver.add(names[2] == 4)
    
    # Clue 8: Bob is the Dane.
    for i in houses:
        solver.add(Implies(names[i] == 2, nats[i] == 3))
    
    # Clue 9: Alice is the Norwegian.
    for i in houses:
        solver.add(Implies(names[i] == 4, nats[i] == 2))
    
    # Clue 3: Peter is not in the first house (index 0; Peter=3).
    solver.add(names[0] != 3)
    
    # Clue 1: The Dragonfruit smoothie lover is somewhere to the left of Eric.
    # Since Dragonfruit is fixed in house index 1, Eric (1) must be in a house with index > 1.
    for i in houses:
        solver.add(Implies(names[i] == 1, i > 1))
    
    # Clue 4: The Dane and the British person are next to each other.
    for i in houses:
        for j in houses:
            solver.add(Implies(And(nats[i] == 3, nats[j] == 4), Or(i == j + 1, i == j - 1)))
    
    # Clue 5: The Desert smoothie lover is not in the fifth house (index 4; desert=0).
    solver.add(smoothies[4] != 0)
    
    # Clue 6: The Swedish person is somewhere to the left of the Dragonfruit smoothie lover.
    # With Dragonfruit fixed at house index 1, the only possibility is that Swedish (1) is in house 0.
    solver.add(nats[0] == 1)
    
    # Clue 7: There are two houses between the person who drinks Lime smoothies and the Dane.
    # Lime smoothie = 2 and Bob (the Dane) = 2 in names.
    for i in houses:
        for j in houses:
            solver.add(Implies(And(smoothies[i] == 2, names[j] == 2), Or(i == j + 3, i == j - 3)))
    
    # Additional deductions to fix positions based on the above clues:
    # Bob must be placed such that the two-house gap holds.
    # Possibilities for Bob (name==2) are house 0, 1, or 3.
    # However, if Bob were in house 0, then Swedish (must be in a house left of index 1) would be forced to be house 0, a contradiction.
    # If Bob were in house 1, then the Dragonfruit smoothie (in house1) would belong to Bob, leaving no neighbor to satisfy the Dane-Brit condition.
    # Thus, Bob must be in house 3.
    for i in houses:
        solver.add(Implies(names[i] == 2, i == 3))
    # This forces the Lime smoothie (2) to be exactly 3 houses away from Bob.
    for i in houses:
        solver.add(Implies(smoothies[i] == 2, i == 0))
    
    # Now, assign the remaining names.
    # Already assigned: House2 (index 2) is Alice (4), and from above Bob (2) is in house3.
    # Remaining names are Arnold (0), Eric (1), and Peter (3).
    # Peter cannot be in house 0 and Eric must be in a house with index > 1 (from Clue 1).
    # This forces: house0 = Arnold (0), house1 = Peter (3), and house4 = Eric (1).
    solver.add(names[0] == 0)  # House 1 gets Arnold.
    solver.add(names[1] == 3)  # House 2 gets Peter.
    solver.add(names[4] == 1)  # House 5 gets Eric.
    
    # Nationality assignments:
    # Already: house0 is Swedish (1) by Clue 6, house2 (Alice) is Norwegian (2) by Clue 9, and house3 (Bob) is Dane (3) by Clue 8.
    # The remaining nationalities are german (0) and brit (4).
    # Clue 4 requires that the Dane (house3) and British person be neighbors.
    # Since house3's neighbors are houses2 and 4, and house2 is already Norwegian, house4 must be British (4).
    solver.add(nats[4] == 4)
    # The remaining nationality for house1 becomes german (0).
    solver.add(nats[1] == 0)
    # (House0, house2, and house3 already have nationalities 1, 2, and 3 respectively.)
    
    # The remaining smoothies (for houses already fixed: house0,1,2, plus the lime condition) become:
    # House0: Lime (2) from our dedicated constraint,
    # House1: Dragonfruit (4) [Clue 2],
    # House2: Watermelon (1) [Clue 11].
    # The remaining two smoothies for houses3 and house4 come from {desert (0), cherry (3)}.
    # With the constraint that the Desert smoothie (0) is not in the fifth house (house4),
    # house4 must be cherry (3) and house3 becomes desert (0).
    # We express this by forcing house4's smoothie to not be 0 (already added) and by distinctness the only possibility.
    # Thus, by the model, the only solution is:
    # House0: 2 (lime), House1: 4 (dragonfruit), House2: 1 (watermelon),
    # House3: 0 (desert), House4: 3 (cherry).
    
    # Solve the puzzle.
    if solver.check() == sat:
        m = solver.model()
        # Reverse mapping dictionaries.
        names_map = {0: "Arnold", 1: "Eric", 2: "Bob", 3: "Peter", 4: "Alice"}
        smoothies_map = {0: "desert", 1: "watermelon", 2: "lime", 3: "cherry", 4: "dragonfruit"}
        nats_map = {0: "german", 1: "swede", 2: "norwegian", 3: "dane", 4: "brit"}
        
        result = {"solution": {"header": ["House", "Name", "Smoothie", "Nationality"], "rows": []}}
        for i in houses:
            house_number = str(i + 1)
            name_val = m[names[i]].as_long()
            smoothie_val = m[smoothies[i]].as_long()
            nat_val = m[nats[i]].as_long()
            row = [house_number, names_map[name_val], smoothies_map[smoothie_val], nats_map[nat_val]]
            result["solution"]["rows"].append(row)
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()