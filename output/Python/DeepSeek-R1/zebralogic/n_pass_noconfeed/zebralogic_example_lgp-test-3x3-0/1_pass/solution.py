import itertools
import json

def main():
    # Define the attributes
    names = ['Peter', 'Eric', 'Arnold']
    educations = ['bachelor', 'associate', 'high school']
    occupations = ['teacher', 'doctor', 'engineer']
    
    # Generate all permutations for each attribute
    for name_perm in itertools.permutations(names):
        for edu_perm in itertools.permutations(educations):
            for occ_perm in itertools.permutations(occupations):
                # Assign attributes to houses (index 0=House1, 1=House2, 2=House3)
                assignment = []
                for i in range(3):
                    assignment.append({
                        'house': str(i+1),
                        'name': name_perm[i],
                        'education': edu_perm[i],
                        'occupation': occ_perm[i]
                    })
                
                # Check constraints
                # Constraint 1: Teacher directly left of associate's degree
                teacher_house = None
                associate_house = None
                for i, house in enumerate(assignment):
                    if house['occupation'] == 'teacher':
                        teacher_house = i
                    if house['education'] == 'associate':
                        associate_house = i
                if teacher_house is None or associate_house is None or teacher_house + 1 != associate_house:
                    continue
                
                # Constraint 2: Associate's degree and Eric are adjacent
                eric_house = None
                for i, house in enumerate(assignment):
                    if house['name'] == 'Eric':
                        eric_house = i
                if eric_house is None or abs(associate_house - eric_house) != 1:
                    continue
                
                # Constraint 3: Peter has high school diploma
                peter_house = None
                for i, house in enumerate(assignment):
                    if house['name'] == 'Peter':
                        peter_house = i
                if peter_house is None or assignment[peter_house]['education'] != 'high school':
                    continue
                
                # Constraint 4: Doctor has bachelor's degree
                doctor_house = None
                for i, house in enumerate(assignment):
                    if house['occupation'] == 'doctor':
                        doctor_house = i
                if doctor_house is None or assignment[doctor_house]['education'] != 'bachelor':
                    continue
                
                # If all constraints passed, format the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Education", "Occupation"],
                        "rows": []
                    }
                }
                for house in assignment:
                    solution["solution"]["rows"].append([
                        house['house'],
                        house['name'],
                        house['education'],
                        house['occupation']
                    ])
                
                # Output the solution as JSON
                print(json.dumps(solution, indent=2))
                return
    
    # If no solution found (shouldn't happen with correct constraints)
    print('{"solution": {"header": ["House", "Name", "Education", "Occupation"], "rows": []}}')

if __name__ == "__main__":
    main()