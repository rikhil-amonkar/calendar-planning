import itertools
import json

# Define the possible values for each category
names = ['Arnold', 'Alice', 'Eric', 'Peter']
hobbies = ['cooking', 'painting', 'photography', 'gardening']
birthdays = ['april', 'jan', 'sept', 'feb']
educations = ['master', 'bachelor', 'associate', 'high school']
smoothies = ['cherry', 'watermelon', 'desert', 'dragonfruit']

# Function to check if a configuration satisfies all constraints
def is_valid(config):
    # Unpack the configuration
    house1, house2, house3, house4 = config
    
    # Constraint 1, 3, 12
    if house1['smoothie'] == 'desert' and house1['birthday'] != 'jan':
        return False
    if house1['birthday'] == 'jan' and house1['education'] != 'bachelor':
        return False
    if house1['birthday'] == 'jan' and house1['smoothie'] != 'desert':
        return False
    if house1['education'] == 'bachelor' and house1['birthday'] != 'jan':
        return False
    if house4['hobby'] == 'painting' and house4['education'] != 'master':
        return False
    if house4['education'] == 'master' and house4['hobby'] != 'painting':
        return False
    if house4['birthday'] == 'feb' and house4['hobby'] != 'painting':
        return False
    if house4['hobby'] == 'painting' and house4['birthday'] != 'feb':
        return False
    
    # Constraint 2
    if house2['name'] == 'Eric' and house2['education'] != 'bachelor':
        return False
    if house2['education'] == 'bachelor' and house2['name'] != 'Eric':
        return False
    
    # Constraint 4, 9
    if house3['education'] == 'high school' and house3['birthday'] != 'sept':
        return False
    if house3['birthday'] == 'sept' and house3['education'] != 'high school':
        return False
    
    # Constraint 5
    if house3['smoothie'] == 'watermelon':
        return False
    
    # Constraint 6
    if house1['name'] == 'Arnold' and house1['education'] != 'associate':
        return False
    if house1['education'] == 'associate' and house1['name'] != 'Arnold':
        return False
    
    # Constraint 7
    if house4['hobby'] == 'painting' and house4['education'] != 'master':
        return False
    if house4['education'] == 'master' and house4['hobby'] != 'painting':
        return False
    
    # Constraint 8
    dragonfruit_house = [house for house in config if house['smoothie'] == 'dragonfruit'][0]
    sept_house = [house for house in config if house['birthday'] == 'sept'][0]
    if abs(config.index(dragonfruit_house) - config.index(sept_house)) != 1:
        return False
    
    # Constraint 10
    if house2['name'] == 'Alice' and house2['hobby'] != 'cooking':
        return False
    if house2['hobby'] == 'cooking' and house2['name'] != 'Alice':
        return False
    
    # Constraint 11
    april_house = [house for house in config if house['birthday'] == 'april'][0]
    gardening_house = [house for house in config if house['hobby'] == 'gardening'][0]
    if abs(config.index(april_house) - config.index(gardening_house)) != 1:
        return False
    
    # All constraints satisfied
    return True

# Generate all possible configurations
all_configs = itertools.permutations([
    {'name': n, 'hobby': h, 'birthday': b, 'education': e, 'smoothie': s}
    for n, h, b, e, s in itertools.product(names, hobbies, birthdays, educations, smoothies)
], 4)

# Filter configurations based on constraints
valid_config = None
for config in all_configs:
    if is_valid(config):
        valid_config = config
        break

# Prepare the output in the required JSON format
output = {
    "solution": {
        "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
        "rows": [
            [str(i+1), house['name'], house['hobby'], house['birthday'], house['education'], house['smoothie']]
            for i, house in enumerate(valid_config)
        ]
    }
}

# Print the JSON output
print(json.dumps(output, indent=2))