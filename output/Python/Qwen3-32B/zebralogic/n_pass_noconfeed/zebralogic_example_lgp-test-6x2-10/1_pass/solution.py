import itertools
import json

names = ['Arnold', 'Eric', 'Peter', 'Alice', 'Bob', 'Carol']
music_genres = ['jazz', 'pop', 'classical', 'rock', 'hip hop', 'country']

solutions = []

for name_perm in itertools.permutations(['Arnold', 'Eric', 'Peter', 'Alice', 'Bob']):
    current_names = list(name_perm) + ['Carol']
    
    # Check if Arnold is not in the fifth house (clue 6)
    if current_names[4] == 'Arnold':
        continue
    
    for music_perm in itertools.permutations(music_genres):
        # Check if music_perm has 'hip hop' in house 3 (index 2) and 'country' in house 6 (index 5)
        if music_perm[2] != 'hip hop' or music_perm[5] != 'country':
            continue
        
        # Check clue 8: Peter's music is pop
        peter_index = current_names.index('Peter')
        if music_perm[peter_index] != 'pop':
            continue
        
        # Check clue 10: one house between Peter and Bob
        bob_index = current_names.index('Bob')
        if abs(peter_index - bob_index) != 2:
            continue
        
        # Check clue 1: Bob directly left of jazz
        if bob_index + 1 >= 6:
            continue
        if music_perm[bob_index + 1] != 'jazz':
            continue
        
        # Check clue 2 and 4: Eric is to the left of hip-hop and adjacent
        eric_index = current_names.index('Eric')
        if eric_index + 1 != 2:  # Eric must be in house 2 (index 1)
            continue
        
        # Check clue 7: Arnold is to the right of pop (Peter's house)
        arnold_index = current_names.index('Arnold')
        if arnold_index <= peter_index:
            continue
        
        # Check clue 11: rock not in fifth house
        rock_index = music_perm.index('rock')
        if rock_index == 4:  # fifth house
            continue
        
        # All constraints passed
        solution_rows = []
        for i in range(6):
            house_num = i + 1
            name = current_names[i]
            music = music_perm[i]
            solution_rows.append([str(house_num), name, music])
        
        solutions.append({
            "solution": {
                "header": ["House", "Name", "MusicGenre"],
                "rows": solution_rows
            }
        })

# Output the first solution found
print(json.dumps(solutions[0], indent=2))