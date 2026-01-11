import itertools
import json

# Define the people and music genres
people = ['Arnold', 'Eric', 'Peter', 'Alice', 'Carol', 'Bob']
music_genres = ['jazz', 'pop', 'classical', 'rock', 'hip hop', 'country']

# Function to check if a given configuration satisfies all the constraints
def is_valid(house_people, house_music):
    # Unpack the configuration into separate lists
    bob_index = house_people.index('Bob')
    eric_index = house_people.index('Eric')
    carol_index = house_people.index('Carol')
    peter_index = house_people.index('Peter')
    hip_hop_index = house_music.index('hip hop')
    jazz_index = house_music.index('jazz')
    pop_index = house_music.index('pop')
    rock_index = house_music.index('rock')

    # Check all constraints
    if bob_index + 1 != jazz_index:  # Bob is directly left of the person who loves jazz music.
        return False
    if eric_index > hip_hop_index:  # Eric is somewhere to the left of the person who loves hip-hop music.
        return False
    if carol_index != 5:  # Carol is in the sixth house.
        return False
    if abs(eric_index - hip_hop_index) != 1:  # Eric and the person who loves hip-hop music are next to each other.
        return False
    if carol_index != house_music.index('country'):  # The person who loves country music is Carol.
        return False
    if house_people[4] == 'Arnold':  # Arnold is not in the fifth house.
        return False
    if peter_index > arnold_index:  # Arnold is somewhere to the right of the person who loves pop music.
        return False
    if house_music[peter_index] != 'pop':  # The person who loves pop music is Peter.
        return False
    if house_music[2] != 'hip hop':  # The person who loves hip-hop music is in the third house.
        return False
    if abs(peter_index - bob_index) != 2:  # There is one house between Peter and Bob.
        return False
    if house_music[4] == 'rock':  # The person who loves rock music is not in the fifth house.
        return False
    
    return True

# Generate all permutations of people and music genres
for house_people in itertools.permutations(people):
    for house_music in itertools.permutations(music_genres):
        if is_valid(house_people, house_music):
            # If valid, prepare the solution in the required JSON format
            solution = {
                "solution": {
                    "header": ["House", "Name", "MusicGenre"],
                    "rows": []
                }
            }
            for i in range(6):
                solution["solution"]["rows"].append([str(i+1), house_people[i], house_music[i]])
            
            # Output the solution as JSON
            print(json.dumps(solution, indent=2))
            break
    else:
        continue
    break