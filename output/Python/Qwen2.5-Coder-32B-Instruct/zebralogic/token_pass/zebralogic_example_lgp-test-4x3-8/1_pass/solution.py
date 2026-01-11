import itertools
import json

# Define the possible values for each attribute
names = ['Eric', 'Arnold', 'Peter', 'Alice']
hair_colors = ['blonde', 'black', 'brown', 'red']
music_genres = ['pop', 'jazz', 'rock', 'classical']

# Function to check if a configuration satisfies all constraints
def is_valid_configuration(config):
    # Unpack the configuration
    (name1, hair1, music1), (name2, hair2, music2), (name3, hair3, music3), (name4, hair4, music4) = config
    
    # Check each constraint
    if name1 == 'Eric' and hair1 != 'red': return False
    if music1 == 'classical' and (music2 != 'blonde' or hair2 != 'blonde'): return False
    if hair3 == 'brown': return False
    if music3 == 'pop': return False
    if music1 != 'classical': return False
    if music1 == 'jazz' and hair1 != 'red': return False
    if name2 == 'Arnold' and music2 != 'rock': return False
    if name3 == 'Arnold' and music3 != 'rock': return False
    if name4 == 'Arnold' and music4 != 'rock': return False
    if names.index(name1) > names.index('Peter'): return False
    if names.index(name2) > names.index('Peter'): return False
    if names.index(name3) > names.index('Peter'): return False
    
    # Ensure all names, hair colors, and music genres are unique
    if len(set([name1, name2, name3, name4])) != 4: return False
    if len(set([hair1, hair2, hair3, hair4])) != 4: return False
    if len(set([music1, music2, music3, music4])) != 4: return False
    
    return True

# Generate all possible configurations
all_configurations = itertools.permutations(names)
valid_configurations = []

for name_perm in all_configurations:
    for hair_perm in itertools.permutations(hair_colors):
        for music_perm in itertools.permutations(music_genres):
            config = list(zip(name_perm, hair_perm, music_perm))
            if is_valid_configuration(config):
                valid_configurations.append(config)

# There should be only one valid configuration
if len(valid_configurations) != 1:
    raise ValueError("Expected exactly one valid configuration, found {}".format(len(valid_configurations)))

# Prepare the solution in the required format
solution = {
    "solution": {
        "header": ["House", "Name", "HairColor", "MusicGenre"],
        "rows": []
    }
}

for i, (name, hair, music) in enumerate(valid_configurations[0], start=1):
    solution["solution"]["rows"].append([str(i), name, hair, music])

# Output the solution as JSON
print(json.dumps(solution, indent=2))