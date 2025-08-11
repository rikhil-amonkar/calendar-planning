import itertools
import json

def main():
    # Define the attributes and their possible values
    names = ['Eric', 'Arnold', 'Peter']
    vacations_other = ['mountain', 'city']  # for houses 1 and 2
    flowers = ['carnations', 'daffodils', 'lilies']
    # Precomputed valid height permutations that satisfy constraints 3 and 6
    height_permutations = [
        ('very short', 'average', 'short'),
        ('very short', 'short', 'average')
    ]
    education_other = ['associate', 'bachelor']  # for houses 0 and 1
    
    # Generate all permutations for names and flowers
    names_perms = list(itertools.permutations(names))
    flower_perms = list(itertools.permutations(flowers))
    # Generate permutations for vacations (houses 1 and 2) and education (houses 0 and 1)
    vacation_perms = list(itertools.permutations(vacations_other))
    education_perms = list(itertools.permutations(education_other))
    
    # Fixed hair colors for all houses
    hair_colors = ['brown', 'black', 'blonde']
    
    solution_found = None
    
    # Iterate over all combinations
    for n in names_perms:
        for vac in vacation_perms:
            # Construct full vacation assignment: house0 is 'beach'
            vacation_assign = ['beach'] + list(vac)
            for h in height_permutations:
                for f in flower_perms:
                    for ed in education_perms:
                        # Construct full education assignment: house2 is 'high school'
                        education_assign = list(ed) + ['high school']
                        
                        # Create the assignment for three houses
                        houses = []
                        for i in range(3):
                            house = {
                                'name': n[i],
                                'vacation': vacation_assign[i],
                                'height': h[i],
                                'flower': f[i],
                                'hair_color': hair_colors[i],
                                'education': education_assign[i]
                            }
                            houses.append(house)
                        
                        # Check constraints
                        if check_constraints(houses):
                            solution_found = houses
                            break
                    if solution_found:
                        break
                if solution_found:
                    break
            if solution_found:
                break
        if solution_found:
            break
    
    # Prepare the output in the required JSON format
    if solution_found:
        header = ["House", "Name", "Vacation", "Height", "Flower", "Hair Color", "Education"]
        rows = []
        for i, house in enumerate(solution_found):
            row = [
                str(i+1),  # House number
                house['name'],
                house['vacation'],
                house['height'],
                house['flower'],
                house['hair_color'],
                house['education']
            ]
            rows.append(row)
        
        output = {"solution": {"header": header, "rows": rows}}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}))

def check_constraints(houses):
    # Constraint 1: Peter has average height
    for house in houses:
        if house['name'] == 'Peter' and house['height'] != 'average':
            return False
    
    # Constraint 2: Arnold loves daffodils
    for house in houses:
        if house['name'] == 'Arnold' and house['flower'] != 'daffodils':
            return False
    
    # Constraint 7: Eric loves lilies
    for house in houses:
        if house['name'] == 'Eric' and house['flower'] != 'lilies':
            return False
    
    # Constraint 8: Lilies and bachelor's degree in the same house (and not house2)
    for i, house in enumerate(houses):
        if house['flower'] == 'lilies':
            if i == 2:  # house2 has fixed 'high school'
                return False
            if house['education'] != 'bachelor':
                return False
    
    # Constraint 9: City vacation is to the right of Peter
    peter_index = None
    for i, house in enumerate(houses):
        if house['name'] == 'Peter':
            peter_index = i
            break
    
    city_index = None
    for i in range(1, 3):  # house0 is beach, so skip
        if houses[i]['vacation'] == 'city':
            city_index = i
            break
    
    if city_index is None or city_index <= peter_index:
        return False
    
    # All constraints satisfied
    return True

if __name__ == "__main__":
    main()