import itertools
import json

def main():
    names = ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob']
    mothers = ['Kailyn', 'Janelle', 'Aniya', 'Penny', 'Holly']
    heights = ['average', 'very short', 'short', 'very tall', 'tall']
    
    for name_perm in itertools.permutations(names):
        # Check constraints that only involve names
        if name_perm.index('Peter') == 1:  # Constraint 4: Peter not in second house
            continue
        if name_perm.index('Eric') == 4:   # Constraint 8: Eric not in fifth house
            continue
            
        for mother_perm in itertools.permutations(mothers):
            # Check constraints involving names and mothers
            if mother_perm[name_perm.index('Alice')] != 'Aniya':  # Constraint 1
                continue
            if name_perm[mother_perm.index('Janelle')] != 'Bob':   # Constraint 3
                continue
            if mother_perm[name_perm.index('Eric')] != 'Kailyn':   # Constraint 10
                continue
                
            for height_perm in itertools.permutations(heights):
                # Check remaining constraints
                if height_perm.index('average') >= mother_perm.index('Penny'):  # Constraint 2
                    continue
                if height_perm.index('short') + 1 != name_perm.index('Arnold'):  # Constraint 5
                    continue
                if name_perm[height_perm.index('very tall')] != 'Arnold':  # Constraint 6
                    continue
                if name_perm.index('Bob') + 1 != height_perm.index('average'):  # Constraint 7
                    continue
                if height_perm.index('very tall') <= mother_perm.index('Holly'):  # Constraint 9
                    continue
                if height_perm.index('very short') != 4:  # Constraint 11
                    continue
                    
                # Build solution
                rows = []
                for i in range(5):
                    rows.append([str(i+1), name_perm[i], mother_perm[i], height_perm[i]])
                
                result = {
                    "solution": {
                        "header": ["House", "Name", "Mother", "Height"],
                        "rows": rows
                    }
                }
                print(json.dumps(result, indent=2))
                return
                
    print('No solution found')

if __name__ == '__main__':
    main()