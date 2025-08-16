from z3 import *
import json

def main():
    s = Solver()

    # We have 5 houses: index 0 corresponds to House 1, index 1 to House 2, …, index 4 to House 5.
    # Each house has attributes: Name, Nationality, Vacation, Education, Occupation.
    # We encode these as integers in the range 0..4 and use the following mappings.

    # Mapping for Names:
    # 0: Eric, 1: Peter, 2: Alice, 3: Bob, 4: Arnold
    ERIC, PETER, ALICE, BOB, ARNOLD = 0, 1, 2, 3, 4

    # Mapping for Nationalities:
    # 0: norwegian, 1: brit, 2: swede, 3: dane, 4: german
    NORWEGIAN, BRIT, SWEDES, DANE, GERMAN = 0, 1, 2, 3, 4

    # Mapping for Vacations:
    # 0: cruise, 1: mountain, 2: camping, 3: beach, 4: city
    CRUISE, MOUNTAIN, CAMPING, BEACH, CITY = 0, 1, 2, 3, 4

    # Mapping for Education:
    # 0: bachelor, 1: master, 2: associate, 3: doctorate, 4: high school
    BACHELOR, MASTER, ASSOCIATE, DOCTORATE, HIGH_SCHOOL = 0, 1, 2, 3, 4

    # Mapping for Occupation:
    # 0: artist, 1: doctor, 2: engineer, 3: teacher, 4: lawyer
    ARTIST, DOCTOR_OCC, ENGINEER, TEACHER, LAWYER = 0, 1, 2, 3, 4

    houses = 5

    # Create lists of Z3 Int variables for each attribute per house (index 0 to 4)
    names = [Int(f"name_{i}") for i in range(houses)]
    nats  = [Int(f"nat_{i}") for i in range(houses)]
    vacs  = [Int(f"vac_{i}") for i in range(houses)]
    edus  = [Int(f"edu_{i}") for i in range(houses)]
    occs  = [Int(f"occ_{i}") for i in range(houses)]
    
    # Domain constraints: each variable is from 0 to 4.
    for i in range(houses):
        s.add(And(names[i] >= 0, names[i] <= 4))
        s.add(And(nats[i]  >= 0, nats[i]  <= 4))
        s.add(And(vacs[i]  >= 0, vacs[i]  <= 4))
        s.add(And(edus[i]  >= 0, edus[i]  <= 4))
        s.add(And(occs[i]  >= 0, occs[i]  <= 4))
    
    # All attributes in each category are all different.
    s.add(Distinct(names))
    s.add(Distinct(nats))
    s.add(Distinct(vacs))
    s.add(Distinct(edus))
    s.add(Distinct(occs))
    
    # ----------------------------------------
    # Now add the clues as constraints.
    # Clue 1: The person who likes going on cruises is the person who is a lawyer.
    # Equivalently: for each house, vac == CRUISE <-> occ == LAWYER.
    for i in range(houses):
        s.add(Implies(vacs[i] == CRUISE, occs[i] == LAWYER))
        s.add(Implies(occs[i] == LAWYER, vacs[i] == CRUISE))
    
    # Clue 2: The person who loves beach vacations is directly left of Arnold.
    # (If a house is Arnold then its left neighbor must have beach;
    #  and if a house has beach then its right neighbor is Arnold.)
    for i in range(houses):
        s.add(Implies(names[i] == ARNOLD, And(i > 0, vacs[i-1] == BEACH)))
    for i in range(houses - 1):
        s.add(Implies(vacs[i] == BEACH, names[i+1] == ARNOLD))
    
    # Clue 3: The person with a doctorate (edu==DOCTORATE) is somewhere to the left of Bob.
    for i in range(houses):
        for j in range(houses):
            s.add(Implies(And(edus[i] == DOCTORATE, names[j] == BOB), i < j))
    
    # Clue 4: The person with an associate's degree (edu==ASSOCIATE) is the person who likes cruises.
    for i in range(houses):
        s.add(Implies(edus[i] == ASSOCIATE, vacs[i] == CRUISE))
        s.add(Implies(vacs[i] == CRUISE, edus[i] == ASSOCIATE))
    
    # Clue 5: Peter is not in the first house.
    s.add(names[0] != PETER)
    
    # Clue 6: The person who is an artist is Peter.
    for i in range(houses):
        s.add(Implies(occs[i] == ARTIST, names[i] == PETER))
        s.add(Implies(names[i] == PETER, occs[i] == ARTIST))
    
    # Clue 7: The person who enjoys camping trips is the person with a master's degree.
    for i in range(houses):
        s.add(Implies(vacs[i] == CAMPING, edus[i] == MASTER))
        s.add(Implies(edus[i] == MASTER, vacs[i] == CAMPING))
    
    # Clue 8: The Dane is somewhere to the right of the person who is a doctor.
    for i in range(houses):
        for j in range(houses):
            s.add(Implies(And(nats[i] == DANE, occs[j] == DOCTOR_OCC), j < i))
    
    # Clue 9: The person with an associate's degree is directly left of the person who is an engineer.
    for i in range(houses - 1):
        s.add(Implies(edus[i] == ASSOCIATE, occs[i+1] == ENGINEER))
    for i in range(1, houses):
        s.add(Implies(occs[i] == ENGINEER, edus[i-1] == ASSOCIATE))
    
    # Clue 10: The person who enjoys camping trips is the British person.
    for i in range(houses):
        s.add(Implies(vacs[i] == CAMPING, nats[i] == BRIT))
        s.add(Implies(nats[i] == BRIT, vacs[i] == CAMPING))
    
    # Clue 11: The Norwegian and the person with a bachelor's degree are next to each other.
    for i in range(houses):
        s.add(Implies(nats[i] == NORWEGIAN, 
                      Or(And(i > 0, edus[i-1] == BACHELOR),
                         And(i < houses - 1, edus[i+1] == BACHELOR))))
    
    # Clue 12: The person who is an artist is the Swedish person.
    for i in range(houses):
        s.add(Implies(occs[i] == ARTIST, nats[i] == SWEDES))
        # Since Peter is the artist (clue 6), we also get that Peter must be Swedish.
        s.add(Implies(names[i] == PETER, nats[i] == SWEDES))
    
    # Clue 13: Bob is not in the fourth house.
    s.add(names[3] != BOB)  # House index 3 corresponds to House 4.
    
    # Clue 14: The person who enjoys camping trips is Eric.
    for i in range(houses):
        s.add(Implies(vacs[i] == CAMPING, names[i] == ERIC))
        s.add(Implies(names[i] == ERIC, vacs[i] == CAMPING))
    
    # Clue 15: Alice is the German.
    for i in range(houses):
        s.add(Implies(names[i] == ALICE, nats[i] == GERMAN))
    
    # Clue 16: The person who loves beach vacations is somewhere to the left of the person who prefers city breaks.
    for i in range(houses):
        for j in range(houses):
            s.add(Implies(And(vacs[i] == BEACH, vacs[j] == CITY), i < j))
    
    # Clue 17: The person who enjoys mountain retreats is in the fifth house.
    s.add(vacs[4] == MOUNTAIN)
    
    # Clue 18: The person who likes going on cruises is somewhere to the right of the person who loves beach vacations.
    for i in range(houses):
        for j in range(houses):
            s.add(Implies(And(vacs[i] == BEACH, vacs[j] == CRUISE), i < j))
    
    # Clue 19: The person with a bachelor's degree is in the third house.
    s.add(edus[2] == BACHELOR)

    # ---------------------------
    # Solve the constraints:
    if s.check() == sat:
        m = s.model()

        # Build mapping dictionaries for output.
        names_map = {ERIC: "Eric", PETER: "Peter", ALICE: "Alice", BOB: "Bob", ARNOLD: "Arnold"}
        nat_map   = {NORWEGIAN: "norwegian", BRIT: "brit", SWEDES: "swede", DANE: "dane", GERMAN: "german"}
        vac_map   = {CRUISE: "cruise", MOUNTAIN: "mountain", CAMPING: "camping", BEACH: "beach", CITY: "city"}
        edu_map   = {BACHELOR: "bachelor", MASTER: "master", ASSOCIATE: "associate", DOCTORATE: "doctorate", HIGH_SCHOOL: "high school"}
        occ_map   = {ARTIST: "artist", DOCTOR_OCC: "doctor", ENGINEER: "engineer", TEACHER: "teacher", LAWYER: "lawyer"}

        solution_rows = []
        # We output houses 1 through 5 in order.
        for i in range(houses):
            house_num = str(i + 1)
            sol_name = names_map[m.evaluate(names[i]).as_long()]
            sol_nat  = nat_map[m.evaluate(nats[i]).as_long()]
            sol_vac  = vac_map[m.evaluate(vacs[i]).as_long()]
            sol_edu  = edu_map[m.evaluate(edus[i]).as_long()]
            sol_occ  = occ_map[m.evaluate(occs[i]).as_long()]
            solution_rows.append([house_num, sol_name, sol_nat, sol_vac, sol_edu, sol_occ])

        result = {
            "solution": {
                "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()