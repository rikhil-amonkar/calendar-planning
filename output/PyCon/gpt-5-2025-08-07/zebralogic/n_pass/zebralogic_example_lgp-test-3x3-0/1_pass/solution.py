import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Domains
    houses = [1, 2, 3]
    names = ["Peter", "Eric", "Arnold"]
    educations = ["bachelor", "associate", "high school"]
    occupations = ["teacher", "doctor", "engineer"]

    # Set up problem
    problem = Problem()
    problem.addVariables(names, houses)
    problem.addVariables(educations, houses)
    problem.addVariables(occupations, houses)

    # Uniqueness within each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), educations)
    problem.addConstraint(AllDifferentConstraint(), occupations)

    # Constraints:
    # 1. Teacher is directly left of Associate (teacher at i, associate at i+1)
    problem.addConstraint(lambda t, a: a - t == 1, ("teacher", "associate"))

    # 2. Associate and Eric are next to each other
    problem.addConstraint(lambda a, e: abs(a - e) == 1, ("associate", "Eric"))

    # 3. Peter has a high school diploma
    problem.addConstraint(lambda p, hs: p == hs, ("Peter", "high school"))

    # 4. Doctor has a bachelor's degree
    problem.addConstraint(lambda d, b: d == b, ("doctor", "bachelor"))

    solutions = problem.getSolutions()

    if not solutions:
        output = {
            "solution": {
                "header": ["House", "Name", "Education", "Occupation"],
                "rows": []
            }
        }
        print(json.dumps(output))
        return

    # Choose the first solution (should be unique for this puzzle)
    s = solutions[0]

    def value_at(category, pos):
        for v in category:
            if s[v] == pos:
                return v
        return None

    rows = []
    for h in houses:
        name = value_at(names, h)
        edu = value_at(educations, h)
        occ = value_at(occupations, h)
        rows.append([str(h), name, edu, occ])

    output = {
        "solution": {
            "header": ["House", "Name", "Education", "Occupation"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()