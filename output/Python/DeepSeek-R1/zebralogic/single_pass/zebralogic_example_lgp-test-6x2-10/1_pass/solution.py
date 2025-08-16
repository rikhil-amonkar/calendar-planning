import itertools
import json

def main():
    all_names = ["Arnold", "Eric", "Peter", "Alice", "Carol", "Bob"]
    all_genres = ["jazz", "pop", "classical", "rock", "hip hop", "country"]
    
    # Fixed positions
    fixed_name_indices = {5: "Carol"}  # House 6 (index 5) is Carol
    fixed_genre_indices = {2: "hip hop", 5: "country"}  # House 3 (index 2) has hip hop, House 6 (index 5) has country
    
    # Prepare remaining names and genres
    remaining_names = [n for n in all_names if n not in fixed_name_indices.values()]
    remaining_genres = [g for g in all_genres if g not in fixed_genre_indices.values()]
    
    # Generate permutations for the non-fixed houses
    for name_perm in itertools.permutations(remaining_names):
        names = list(name_perm)
        names.append(fixed_name_indices[5])  # Add Carol at index 5
        
        # Eric must be in house 2 (index 1) due to constraints 2 and 4
        if names[1] != "Eric":
            continue
        # Arnold cannot be in house 5 (index 4) due to constraint 6
        if names[4] == "Arnold":
            continue
        
        for genre_perm in itertools.permutations(remaining_genres):
            genres = [None] * 6
            genres[2] = fixed_genre_indices[2]  # hip hop at index 2
            genres[5] = fixed_genre_indices[5]  # country at index 5
            genres[0] = genre_perm[0]
            genres[1] = genre_perm[1]
            genres[3] = genre_perm[2]
            genres[4] = genre_perm[3]
            
            # Constraint 11: Rock not in fifth house (index 4)
            if genres[4] == "rock":
                continue
            
            # Constraint 1: Bob directly left of jazz
            try:
                bob_index = names.index("Bob")
            except ValueError:
                continue
            if bob_index == 5:  # Bob cannot be in the last house
                continue
            if genres[bob_index + 1] != "jazz":
                continue
            
            # Constraint 7: Arnold right of pop
            try:
                pop_index = genres.index("pop")
            except ValueError:
                continue
            try:
                arnold_index = names.index("Arnold")
            except ValueError:
                continue
            if arnold_index <= pop_index:
                continue
            
            # Constraint 8: Peter has pop
            try:
                peter_index = names.index("Peter")
            except ValueError:
                continue
            if genres[peter_index] != "pop":
                continue
            
            # Constraint 10: One house between Peter and Bob
            if abs(peter_index - bob_index) != 2:
                continue
            
            # All constraints satisfied, prepare output
            header = ["House", "Name", "MusicGenre"]
            rows = []
            for i in range(6):
                house_num = str(i + 1)
                name_val = names[i]
                genre_val = genres[i]
                rows.append([house_num, name_val, genre_val])
            
            solution_dict = {
                "solution": {
                    "header": header,
                    "rows": rows
                }
            }
            print(json.dumps(solution_dict))
            return
    
    # If no solution found
    print(json.dumps({"solution": {}}))

if __name__ == "__main__":
    main()