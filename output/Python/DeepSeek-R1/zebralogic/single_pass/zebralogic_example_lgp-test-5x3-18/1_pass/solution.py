import json

def main():
    names = [set(['Alice', 'Eric', 'Arnold', 'Bob', 'Peter']) for _ in range(5)]
    flowers = [set(['tulips', 'roses', 'lilies', 'daffodils', 'carnations']) for _ in range(5)]
    animals = [set(['dog', 'horse', 'cat', 'bird', 'fish']) for _ in range(5)]
    
    def fix_attribute(attr, index, value):
        for i in range(5):
            if i == index:
                attr[i] = {value}
            else:
                if value in attr[i]:
                    attr[i].remove(value)
    
    # Apply clue 1: Alice is in the second house (index 1)
    fix_attribute(names, 1, 'Alice')
    
    # Apply clue 8: Alice is directly left of the person who keeps horses -> horses in house 3 (index 2)
    fix_attribute(animals, 2, 'horse')
    
    # Apply clue 5: The person who keeps horses is Eric -> Eric in house 3 (index 2)
    fix_attribute(names, 2, 'Eric')
    
    # Apply clue 7: The fish enthusiast is directly left of Bob -> Bob in house 5 (index 4), fish in house 4 (index 3)
    fix_attribute(names, 4, 'Bob')
    fix_attribute(animals, 3, 'fish')
    
    # Apply clue 4: The fish enthusiast loves daffodils -> daffodils in house 4 (index 3)
    fix_attribute(flowers, 3, 'daffodils')
    
    # Apply clue 6: Two houses between dog owner and Bob -> Bob in house 5, so dog in house 2 (index 1)
    fix_attribute(animals, 1, 'dog')
    
    # Apply clue 10: Cat not in first house (index 0)
    animals[0].discard('cat')
    fix_attribute(animals, 0, 'bird')
    
    # Remaining animal (cat) must be in house 5 (index 4)
    fix_attribute(animals, 4, 'cat')
    
    # Apply clue 2: Lilies lover is the bird keeper -> bird in house 1 (index 0), so lilies in house 1
    fix_attribute(flowers, 0, 'lilies')
    
    # Apply clue 9: Carnations directly left of tulips -> only possible at houses 2 (index 1) and 3 (index 2)
    fix_attribute(flowers, 1, 'carnations')
    fix_attribute(flowers, 2, 'tulips')
    
    # Remaining flower (roses) in house 5 (index 4)
    fix_attribute(flowers, 4, 'roses')
    
    # Apply clue 3: Peter is right of tulips lover (index 2) -> Peter in house 4 (index 3)
    fix_attribute(names, 3, 'Peter')
    
    # Remaining name (Arnold) in house 1 (index 0)
    fix_attribute(names, 0, 'Arnold')
    
    # Prepare the solution rows
    rows = []
    for i in range(5):
        house_num = str(i+1)
        name_val = next(iter(names[i]))
        flower_val = next(iter(flowers[i]))
        animal_val = next(iter(animals[i]))
        rows.append([house_num, name_val, flower_val, animal_val])
    
    # Create the solution dictionary
    solution_dict = {
        "solution": {
            "header": ["House", "Name", "Flower", "Animal"],
            "rows": rows
        }
    }
    
    # Output the solution as JSON
    print(json.dumps(solution_dict))

if __name__ == "__main__":
    main()