import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()

    houses = [1, 2, 3, 4, 5]

    names = ["Eric", "Peter", "Alice", "Bob", "Arnold"]
    nationalities = ["norwegian", "brit", "swede", "dane", "german"]
    vacations = ["cruise", "mountain", "camping", "beach", "city"]
    educations = ["bachelor", "master", "associate", "doctorate", "high school"]
    occupations = ["artist", "doctor", "engineer", "teacher", "lawyer"]

    # Add variables for each item with domain houses
    for group in [names, nationalities, vacations, educations, occupations]:
        for item in group:
            problem.addVariable(item, houses)
        problem.addConstraint(AllDifferentConstraint(), group)

    # Constraints:

    # 1. The person who likes going on cruises is the person who is a lawyer.
    problem.addConstraint(lambda c, l: c == l, ("cruise", "lawyer"))

    # 2. The person who loves beach vacations is directly left of Arnold.
    problem.addConstraint(lambda b, a: b + 1 == a, ("beach", "Arnold"))

    # 3. The person with a doctorate is somewhere to the left of Bob.
    problem.addConstraint(lambda d, b: d < b, ("doctorate", "Bob"))

    # 4. The person with an associate's degree is the person who likes going on cruises.
    problem.addConstraint(lambda a, c: a == c, ("associate", "cruise"))

    # 5. Peter is not in the first house.
    problem.addConstraint(lambda p: p != 1, ("Peter",))

    # 6. The person who is an artist is Peter.
    problem.addConstraint(lambda art, peter: art == peter, ("artist", "Peter"))

    # 7. The person who enjoys camping trips is the person with a master's degree.
    problem.addConstraint(lambda camp, m: camp == m, ("camping", "master"))

    # 8. The Dane is somewhere to the right of the person who is a doctor.
    problem.addConstraint(lambda dane, doc: dane > doc, ("dane", "doctor"))

    # 9. The person with an associate's degree is directly left of the person who is an engineer.
    problem.addConstraint(lambda assoc, eng: assoc + 1 == eng, ("associate", "engineer"))

    # 10. The person who enjoys camping trips is the British person.
    problem.addConstraint(lambda camp, brit: camp == brit, ("camping", "brit"))

    # 11. The Norwegian and the person with a bachelor's degree are next to each other.
    problem.addConstraint(lambda nor, bach: abs(nor - bach) == 1, ("norwegian", "bachelor"))

    # 12. The person who is an artist is the Swedish person.
    problem.addConstraint(lambda art, sw: art == sw, ("artist", "swede"))

    # 13. Bob is not in the fourth house.
    problem.addConstraint(lambda b: b != 4, ("Bob",))

    # 14. The person who enjoys camping trips is Eric.
    problem.addConstraint(lambda camp, eric: camp == eric, ("camping", "Eric"))

    # 15. Alice is the German.
    problem.addConstraint(lambda alice, ger: alice == ger, ("Alice", "german"))

    # 16. The person who loves beach vacations is somewhere to the left of the person who prefers city breaks.
    problem.addConstraint(lambda beach, city: beach < city, ("beach", "city"))

    # 17. The person who enjoys mountain retreats is in the fifth house.
    problem.addConstraint(lambda m: m == 5, ("mountain",))

    # 18. The person who likes going on cruises is somewhere to the right of the person who loves beach vacations.
    problem.addConstraint(lambda cruise, beach: cruise > beach, ("cruise", "beach"))

    # 19. The person with a bachelor's degree is in the third house.
    problem.addConstraint(lambda b: b == 3, ("bachelor",))

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found for the puzzle.")

    sol = solutions[0]

    # Build rows by house
    rows = []
    for h in houses:
        # Find the unique item in each category at house h
        name = next(n for n in names if sol[n] == h)
        nationality = next(nat for nat in nationalities if sol[nat] == h)
        vacation = next(v for v in vacations if sol[v] == h)
        education = next(ed for ed in educations if sol[ed] == h)
        occupation = next(oc for oc in occupations if sol[oc] == h)

        rows.append([str(h), name, nationality, vacation, education, occupation])

    output = {
        "solution": {
            "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_puzzle()