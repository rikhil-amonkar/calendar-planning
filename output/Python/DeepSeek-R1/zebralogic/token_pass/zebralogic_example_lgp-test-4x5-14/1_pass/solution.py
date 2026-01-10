import itertools
import json

def main():
    # Define the attributes and their domains
    attributes = {
        'name': ['Peter', 'Alice', 'Eric', 'Arnold'],
        'mother': ['Janelle', 'Holly', 'Aniya', 'Kailyn'],
        'smoothie': ['watermelon', 'dragonfruit', 'desert', 'cherry'],
        'height': ['tall', 'average', 'short', 'very short'],
        'education': ['high school', 'associate', 'master', 'bachelor']
    }
    
    # Initialize solution variables
    solution_found = None
    
    # Generate all permutations for each attribute, applying fixed constraints
    for name_perm in itertools.permutations(attributes['name']):
        if name_perm[2] != 'Alice':
            continue
            
        for mother_perm in itertools.permutations(attributes['mother']):
            if mother_perm[2] != 'Janelle':
                continue
                
            for smoothie_perm in itertools.permutations(attributes['smoothie']):
                for height_perm in itertools.permutations(attributes['height']):
                    if height_perm[2] != 'tall':
                        continue
                        
                    for education_perm in itertools.permutations(attributes['education']):
                        # Check all constraints
                        # Constraint 2: Desert smoothie lover has master's degree
                        desert_index = None
                        for i, s in enumerate(smoothie_perm):
                            if s == 'desert':
                                desert_index = i
                                break
                        if desert_index is None or education_perm[desert_index] != 'master':
                            continue
                            
                        # Constraint 3: Desert smoothie not in first house
                        if smoothie_perm[0] == 'desert':
                            continue
                            
                        # Constraint 4: Very short left of high school
                        very_short_index = None
                        high_school_index = None
                        for i, h in enumerate(height_perm):
                            if h == 'very short':
                                very_short_index = i
                            if education_perm[i] == 'high school':
                                high_school_index = i
                        if very_short_index is None or high_school_index is None or very_short_index >= high_school_index:
                            continue
                            
                        # Constraint 5: Eric and cherry smoothie adjacent
                        eric_index = None
                        cherry_index = None
                        for i, n in enumerate(name_perm):
                            if n == 'Eric':
                                eric_index = i
                        for i, s in enumerate(smoothie_perm):
                            if s == 'cherry':
                                cherry_index = i
                        if eric_index is None or cherry_index is None or abs(eric_index - cherry_index) != 1:
                            continue
                            
                        # Constraint 6: High school not in third house
                        if education_perm[2] == 'high school':
                            continue
                            
                        # Constraint 7: Mother Kailyn has associate degree
                        kailyn_index = None
                        for i, m in enumerate(mother_perm):
                            if m == 'Kailyn':
                                kailyn_index = i
                                break
                        if kailyn_index is None or education_perm[kailyn_index] != 'associate':
                            continue
                            
                        # Constraint 8: Cherry smoothie has mother Aniya
                        cherry_mother_index = None
                        for i, s in enumerate(smoothie_perm):
                            if s == 'cherry':
                                cherry_mother_index = i
                                break
                        if cherry_mother_index is None or mother_perm[cherry_mother_index] != 'Aniya':
                            continue
                            
                        # Constraint 9: Already enforced by fixed values
                        
                        # Constraint 10: Arnold right of average height
                        arnold_index = None
                        average_index = None
                        for i, n in enumerate(name_perm):
                            if n == 'Arnold':
                                arnold_index = i
                        for i, h in enumerate(height_perm):
                            if h == 'average':
                                average_index = i
                        if arnold_index is None or average_index is None or arnold_index <= average_index:
                            continue
                            
                        # Constraint 11: Dragonfruit directly left of short
                        dragonfruit_index = None
                        short_index = None
                        for i, s in enumerate(smoothie_perm):
                            if s == 'dragonfruit':
                                dragonfruit_index = i
                        for i, h in enumerate(height_perm):
                            if h == 'short':
                                short_index = i
                        if dragonfruit_index is None or short_index is None or dragonfruit_index + 1 != short_index:
                            continue
                            
                        # Constraint 12: Already enforced by fixed values
                        
                        # If we reach here, all constraints are satisfied
                        solution_found = {
                            'name': name_perm,
                            'mother': mother_perm,
                            'smoothie': smoothie_perm,
                            'height': height_perm,
                            'education': education_perm
                        }
                        break
                    if solution_found:
                        break
                if solution_found:
                    break
            if solution_found:
                break
        if solution_found:
            break
            
    # Format the solution as JSON
    if solution_found:
        rows = []
        for i in range(4):
            row = [
                str(i+1),
                solution_found['name'][i],
                solution_found['mother'][i],
                solution_found['smoothie'][i],
                solution_found['height'][i],
                solution_found['education'][i]
            ]
            rows.append(row)
        
        output = {
            "solution": {
                "header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"],
                "rows": rows
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()