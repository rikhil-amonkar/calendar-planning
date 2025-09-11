import itertools
import json

def main():
    names = ['Peter', 'Alice', 'Bob', 'Eric', 'Arnold']
    heights = ['very tall', 'average', 'tall', 'very short', 'short']
    
    for name_perm in itertools.permutations(names):
        # Check clue 5: Alice is directly left of average height (house 4)
        if name_perm[3] != 'Alice':
            continue
        
        for height_perm in itertools.permutations(heights):
            # Check clue 1: house 2 is short, clue 7: house 5 is average
            if height_perm[1] != 'short' or height_perm[4] != 'average':
                continue
            
            # Check clue 6: short (house 2) and very short are adjacent
            if not (height_perm[0] == 'very short' or height_perm[2] == 'very short'):
                continue
            
            # Check clue 2: Peter directly left of Bob
            peter_pos = -1
            bob_pos = -1
            for i in range(4):  # i+1 must be within 5 houses
                if name_perm[i] == 'Peter' and name_perm[i+1] == 'Bob':
                    peter_pos = i
                    bob_pos = i+1
                    break
            if peter_pos == -1:
                continue  # No Peter left of Bob
            
            # Check clue 3: Eric is left of Peter
            eric_pos = name_perm.index('Eric')
            if eric_pos >= peter_pos:
                continue
            
            # Check clue 4: very tall directly left of Peter
            vt_pos = height_perm.index('very tall')
            if vt_pos != peter_pos - 1:
                continue
            
            # Build solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "Height"],
                    "rows": []
                }
            }
            for i in range(5):
                house_num = i + 1
                name = name_perm[i]
                height = height_perm[i]
                solution["solution"]["rows"].append([
                    str(house_num), name, height
                ])
            
            print(json.dumps(solution, indent=2))
            return
    
    # Fallback if no solution found
    print(json.dumps({"solution": {"header": [], "rows": []}}))

if __name__ == "__main__":
    main()