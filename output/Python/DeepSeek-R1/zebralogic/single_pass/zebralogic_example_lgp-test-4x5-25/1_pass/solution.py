import json

def satisfies_all_constraints(state):
    # Clue 2: Alice loves romance books
    found_clue2 = False
    for i in range(4):
        if state['names'][i] == 'Alice' and state['book_genres'][i] == 'romance':
            found_clue2 = True
    if not found_clue2:
        return False

    # Clue 5: Ranch house is to the right of red hair
    ranch_index = None
    red_hair_index = None
    for i in range(4):
        if state['house_styles'][i] == 'ranch':
            ranch_index = i
        if state['hair_colors'][i] == 'red':
            red_hair_index = i
    if ranch_index is None or red_hair_index is None:
        return False
    if ranch_index <= red_hair_index:
        return False

    # Clue 6: Peter has child Bella
    for i in range(4):
        if state['names'][i] == 'Peter':
            if state['children'][i] != 'Bella':
                return False

    # Clue 7: Arnold has red hair
    for i in range(4):
        if state['names'][i] == 'Arnold':
            if state['hair_colors'][i] != 'red':
                return False

    # Clue 8: Alice is in colonial house
    for i in range(4):
        if state['names'][i] == 'Alice':
            if state['house_styles'][i] != 'colonial':
                return False

    # Clue 10: Peter loves fantasy books
    for i in range(4):
        if state['book_genres'][i] == 'fantasy':
            if state['names'][i] != 'Peter':
                return False

    # Clue 11: Arnold has child Meredith
    for i in range(4):
        if state['names'][i] == 'Arnold':
            if state['children'][i] != 'Meredith':
                return False

    # Clue 13: Arnold loves science fiction
    for i in range(4):
        if state['book_genres'][i] == 'science fiction':
            if state['names'][i] != 'Arnold':
                return False

    return True

def main():
    base_state = {
        'names': [None, 'Eric', None, None],
        'house_styles': [None, None, 'craftsman', None],
        'hair_colors': [None, 'black', None, 'brown'],
        'children': [None, None, None, 'Samantha'],
        'book_genres': [None, None, None, None]
    }
    
    available = {
        'names': set(['Arnold', 'Peter', 'Alice']),
        'house_styles': set(['colonial', 'victorian', 'ranch']),
        'hair_colors': set(['red', 'blonde']),
        'children': set(['Bella', 'Fred', 'Meredith']),
        'book_genres': set(['mystery', 'fantasy', 'romance', 'science fiction'])
    }
    
    found = False
    solution_state = None
    
    for name0 in available['names']:
        if found: break
        for house_style0 in available['house_styles']:
            if found: break
            for hair_color0 in available['hair_colors']:
                if found: break
                for child0 in available['children']:
                    if found: break
                    for book_genre0 in available['book_genres']:
                        if found: break
                        
                        candidate = {
                            'names': base_state['names'][:],
                            'house_styles': base_state['house_styles'][:],
                            'hair_colors': base_state['hair_colors'][:],
                            'children': base_state['children'][:],
                            'book_genres': base_state['book_genres'][:]
                        }
                        candidate['names'][0] = name0
                        candidate['house_styles'][0] = house_style0
                        candidate['hair_colors'][0] = hair_color0
                        candidate['children'][0] = child0
                        candidate['book_genres'][0] = book_genre0
                        
                        avail_house_style1 = available['house_styles'] - {house_style0}
                        for house_style1 in avail_house_style1:
                            if found: break
                            candidate['house_styles'][1] = house_style1
                            
                            avail_children1 = available['children'] - {child0}
                            for child1 in avail_children1:
                                if found: break
                                candidate['children'][1] = child1
                                
                                avail_book_genres1 = available['book_genres'] - {book_genre0}
                                for book_genre1 in avail_book_genres1:
                                    if found: break
                                    candidate['book_genres'][1] = book_genre1
                                    
                                    avail_names2 = available['names'] - {name0}
                                    for name2 in avail_names2:
                                        if found: break
                                        candidate['names'][2] = name2
                                        
                                        avail_hair_colors2 = available['hair_colors'] - {hair_color0}
                                        if len(avail_hair_colors2) != 1:
                                            continue
                                        hair_color2 = next(iter(avail_hair_colors2))
                                        candidate['hair_colors'][2] = hair_color2
                                        
                                        avail_children2 = available['children'] - {child0, child1}
                                        if len(avail_children2) != 1:
                                            continue
                                        child2 = next(iter(avail_children2))
                                        candidate['children'][2] = child2
                                        
                                        avail_book_genres2 = available['book_genres'] - {book_genre0, book_genre1}
                                        for book_genre2 in avail_book_genres2:
                                            candidate['book_genres'][2] = book_genre2
                                            
                                            avail_names3 = available['names'] - {name0, name2}
                                            if len(avail_names3) != 1:
                                                continue
                                            name3 = next(iter(avail_names3))
                                            candidate['names'][3] = name3
                                            
                                            avail_house_style3 = available['house_styles'] - {house_style0, house_style1}
                                            if len(avail_house_style3) != 1:
                                                continue
                                            house_style3 = next(iter(avail_house_style3))
                                            candidate['house_styles'][3] = house_style3
                                            
                                            avail_book_genres3 = available['book_genres'] - {book_genre0, book_genre1, book_genre2}
                                            if len(avail_book_genres3) != 1:
                                                continue
                                            book_genre3 = next(iter(avail_book_genres3))
                                            candidate['book_genres'][3] = book_genre3
                                            
                                            if satisfies_all_constraints(candidate):
                                                solution_state = candidate
                                                found = True
                                                break
                                    
    if solution_state is None:
        print("No solution found")
        return
    
    rows = []
    for i in range(4):
        row = [
            str(i+1),
            solution_state['names'][i],
            solution_state['house_styles'][i],
            solution_state['hair_colors'][i],
            solution_state['children'][i],
            solution_state['book_genres'][i]
        ]
        rows.append(row)
    
    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
            "rows": rows
        }
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()