import itertools
import json

# Define the possible values for each characteristic
names = ['Arnold', 'Eric']
occupations = ['engineer', 'doctor']
birthdays = ['april', 'sept']
house_styles = ['victorian', 'colonial']
heights = ['very short', 'short']
cigars = ['pall mall', 'prince']

# Generate all possible permutations of assignments for two houses
all_permutations = list(itertools.permutations(names))
all_combinations = list(itertools.product(
    all_permutations,
    list(itertools.permutations(occupations)),
    list(itertools.permutations(birthdays)),
    list(itertools.permutations(house_styles)),
    list(itertools.permutations(heights)),
    list(itertools.permutations(cigars))
))

def is_valid_solution(combination):
    # Unpack the combination
    (name1, name2), (occupation1, occupation2), (birthday1, birthday2), \
    (house_style1, house_style2), (height1, height2), (cigar1, cigar2) = combination
    
    # Apply constraints
    # Constraint 1: The person who is an engineer is in the first house.
    if occupation1 != 'engineer':
        return False
    
    # Constraint 2: The person whose birthday is in April and the person who is a doctor are next to each other.
    if (birthday1 == 'april' and occupation2 != 'doctor') and (birthday2 == 'april' and occupation1 != 'doctor'):
        return False
    
    # Constraint 3: The person living in a colonial-style house is the person who is an engineer.
    if house_style1 != 'colonial':
        return False
    
    # Constraint 4: The person who is very short is the person who is an engineer.
    if height1 != 'very short':
        return False
    
    # Constraint 5: The person who is short is the person partial to Pall Mall.
    if height2 != 'short' or cigar2 != 'pall mall':
        return False
    
    # Constraint 6: The person who is an engineer is Eric.
    if name1 != 'Eric':
        return False
    
    return True

# Find the valid solution
for combination in all_combinations:
    if is_valid_solution(combination):
        (name1, name2), (occupation1, occupation2), (birthday1, birthday2), \
        (house_style1, house_style2), (height1, height2), (cigar1, cigar2) = combination
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"],
                "rows": [
                    ["1", name1, occupation1, birthday1, house_style1, height1, cigar1],
                    ["2", name2, occupation2, birthday2, house_style2, height2, cigar2]
                ]
            }
        }
        
        # Print the solution as JSON
        print(json.dumps(solution, indent=2))
        break