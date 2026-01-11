import itertools
import json

def is_valid(arrangement):
    # Unpack the arrangement into separate lists
    names = [house['name'] for house in arrangement]
    heights = [house['height'] for house in arrangement]
    phones = [house['phone_model'] for house in arrangement]
    
    # Apply each constraint
    # 1. Bob is directly left of the person who is tall.
    if names.index('Bob') + 1 != heights.index('tall'):
        return False
    
    # 2. Peter is somewhere to the left of the person who uses an iPhone 13.
    if names.index('Peter') >= phones.index('iphone 13'):
        return False
    
    # 3. The person who is very short is somewhere to the right of the person who uses a Google Pixel 6.
    if heights.index('very short') <= phones.index('google pixel 6'):
        return False
    
    # 4. Carol is the person who is very tall.
    if names[heights.index('very tall')] != 'Carol':
        return False
    
    # 5. There is one house between the person who uses a Google Pixel 6 and the person who is short.
    if abs(phones.index('google pixel 6') - heights.index('short')) != 2:
        return False
    
    # 6. The person who uses a Samsung Galaxy S21 is not in the first house.
    if phones[0] == 'samsung galaxy s21':
        return False
    
    # 7. The person who uses a OnePlus 9 is directly left of the person who is short.
    if phones.index('oneplus 9') + 1 != heights.index('short'):
        return False
    
    # 8. The person who is tall is Arnold.
    if names[heights.index('tall')] != 'Arnold':
        return False
    
    # 9. The person who is super tall is in the first house.
    if heights[0] != 'super tall':
        return False
    
    # 10. The person who uses a Xiaomi Mi 11 is Carol.
    if names[phones.index('xiaomi mi 11')] != 'Carol':
        return False
    
    # 11. The person who uses a Google Pixel 6 is somewhere to the right of Eric.
    if phones.index('google pixel 6') <= names.index('Eric'):
        return False
    
    # 12. The person who is short is in the sixth house.
    if heights[5] != 'short':
        return False
    
    return True

def solve_puzzle():
    # Define the possible values for each attribute
    names = ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold', 'Carol']
    heights = ['very tall', 'tall', 'super tall', 'average', 'very short', 'short']
    phones = ['oneplus 9', 'google pixel 6', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'xiaomi mi 11']
    
    # Generate all possible permutations for each attribute
    for name_perm in itertools.permutations(names):
        for height_perm in itertools.permutations(heights):
            for phone_perm in itertools.permutations(phones):
                # Create the arrangement
                arrangement = [{'name': name_perm[i], 'height': height_perm[i], 'phone_model': phone_perm[i]} for i in range(6)]
                
                # Check if the arrangement is valid
                if is_valid(arrangement):
                    # Format the solution as required
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Height", "PhoneModel"],
                            "rows": [[str(i+1), arrangement[i]['name'], arrangement[i]['height'], arrangement[i]['phone_model']] for i in range(6)]
                        }
                    }
                    return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())