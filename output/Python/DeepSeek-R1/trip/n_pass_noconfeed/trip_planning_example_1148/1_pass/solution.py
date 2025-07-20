import itertools
import json

def main():
    direct_edges = [
        ('Dubrovnik', 'Stockholm'),
        ('Lisbon', 'Copenhagen'),
        ('Lisbon', 'Lyon'),
        ('Copenhagen', 'Stockholm'),
        ('Copenhagen', 'Split'),
        ('Prague', 'Stockholm'),
        ('Tallinn', 'Stockholm'),
        ('Prague', 'Lyon'),
        ('Lisbon', 'Stockholm'),
        ('Prague', 'Lisbon'),
        ('Stockholm', 'Split'),
        ('Prague', 'Copenhagen'),
        ('Split', 'Lyon'),
        ('Copenhagen', 'Dubrovnik'),
        ('Prague', 'Split'),
        ('Tallinn', 'Copenhagen'),
        ('Tallinn', 'Prague')
    ]
    direct_set = set(frozenset(pair) for pair in direct_edges)
    
    durations = [2, 2, 3, 3, 4, 5, 5]
    unique_assignments = set(itertools.permutations(durations))
    
    for assignment in unique_assignments:
        d1, d2, d3, d4, d5, d6, d7 = assignment
        t1 = d1
        t2 = t1 + d2 - 1
        t3 = t2 + d3 - 1
        t4 = t3 + d4 - 1
        t5 = t4 + d5 - 1
        t6 = t5 + d6 - 1
        
        if not (1 <= t1 < t2 < t3 < t4 < t5 < t6 <= 17):
            continue
        if d7 != 19 - t6:
            continue
            
        index_4 = [i for i in range(7) if assignment[i] == 4]
        if len(index_4) != 1:
            continue
        index_4 = index_4[0]
        index_5 = [i for i in range(7) if assignment[i] == 5]
        index_3 = [i for i in range(7) if assignment[i] == 3]
        index_2 = [i for i in range(7) if assignment[i] == 2]
        
        for perm5 in itertools.permutations(['Dubrovnik','Copenhagen']):
            for perm3 in itertools.permutations(['Prague','Split']):
                for perm2 in itertools.permutations(['Tallinn','Lisbon']):
                    cities_arr = [None] * 7
                    cities_arr[index_4] = 'Stockholm'
                    if len(index_5) == 2:
                        cities_arr[index_5[0]] = perm5[0]
                        cities_arr[index_5[1]] = perm5[1]
                    if len(index_3) == 2:
                        cities_arr[index_3[0]] = perm3[0]
                        cities_arr[index_3[1]] = perm3[1]
                    if len(index_2) == 2:
                        cities_arr[index_2[0]] = perm2[0]
                        cities_arr[index_2[1]] = perm2[1]
                    
                    valid = True
                    for i in range(6):
                        a = cities_arr[i]
                        b = cities_arr[i+1]
                        if frozenset([a, b]) not in direct_set:
                            valid = False
                            break
                    if not valid:
                        continue
                    if frozenset([cities_arr[6], 'Lyon']) not in direct_set:
                        continue
                    
                    try:
                        tallinn_index = cities_arr.index('Tallinn')
                    except ValueError:
                        valid = False
                    else:
                        if tallinn_index == 1:
                            if not (t1 <= 2):
                                valid = False
                        elif tallinn_index == 2:
                            if not (t2 <= 2):
                                valid = False
                        elif tallinn_index >= 3:
                            valid = False
                    if not valid:
                        continue
                    
                    try:
                        lisbon_index = cities_arr.index('Lisbon')
                    except ValueError:
                        valid = False
                    else:
                        if lisbon_index == 0:
                            if not (t1 >= 4):
                                valid = False
                        elif lisbon_index == 1:
                            if not (t1 <= 5 and t2 >= 4):
                                valid = False
                        elif lisbon_index == 2:
                            if not (t2 <= 5 and t3 >= 4):
                                valid = False
                        elif lisbon_index == 3:
                            if not (t3 <= 5 and t4 >= 4):
                                valid = False
                        elif lisbon_index == 4:
                            if not (t4 <= 5 and t5 >= 4):
                                valid = False
                        elif lisbon_index == 5:
                            if not (t5 <= 5 and t6 >= 4):
                                valid = False
                        elif lisbon_index == 6:
                            if not (t6 <= 5):
                                valid = False
                    if not valid:
                        continue
                    
                    try:
                        stockholm_index = cities_arr.index('Stockholm')
                    except ValueError:
                        valid = False
                    else:
                        if stockholm_index == 0:
                            if not (t1 >= 13):
                                valid = False
                        elif stockholm_index == 1:
                            if not (t1 <= 16 and t2 >= 13):
                                valid = False
                        elif stockholm_index == 2:
                            if not (t2 <= 16 and t3 >= 13):
                                valid = False
                        elif stockholm_index == 3:
                            if not (t3 <= 16 and t4 >= 13):
                                valid = False
                        elif stockholm_index == 4:
                            if not (t4 <= 16 and t5 >= 13):
                                valid = False
                        elif stockholm_index == 5:
                            if not (t5 <= 16 and t6 >= 13):
                                valid = False
                        elif stockholm_index == 6:
                            if not (t6 <= 16):
                                valid = False
                    if not valid:
                        continue
                    
                    itinerary = []
                    if t1 == 1:
                        day_str = "1"
                    else:
                        day_str = f"1-{t1}"
                    itinerary.append({"day_range": f"Day {day_str}", "place": cities_arr[0]})
                    
                    if t1 == t2:
                        day_str = f"{t1}"
                    else:
                        day_str = f"{t1}-{t2}"
                    itinerary.append({"day_range": f"Day {day_str}", "place": cities_arr[1]})
                    
                    if t2 == t3:
                        day_str = f"{t2}"
                    else:
                        day_str = f"{t2}-{t3}"
                    itinerary.append({"day_range": f"Day {day_str}", "place": cities_arr[2]})
                    
                    if t3 == t4:
                        day_str = f"{t3}"
                    else:
                        day_str = f"{t3}-{t4}"
                    itinerary.append({"day_range": f"Day {day_str}", "place": cities_arr[3]})
                    
                    if t4 == t5:
                        day_str = f"{t4}"
                    else:
                        day_str = f"{t4}-{t5}"
                    itinerary.append({"day_range": f"Day {day_str}", "place": cities_arr[4]})
                    
                    if t5 == t6:
                        day_str = f"{t5}"
                    else:
                        day_str = f"{t5}-{t6}"
                    itinerary.append({"day_range": f"Day {day_str}", "place": cities_arr[5]})
                    
                    if t6 == 18:
                        day_str = "18"
                    else:
                        day_str = f"{t6}-18"
                    itinerary.append({"day_range": f"Day {day_str}", "place": cities_arr[6]})
                    
                    itinerary.append({"day_range": "Day 18-19", "place": "Lyon"})
                    
                    print(json.dumps({"itinerary": itinerary}, indent=2))
                    return
                    
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()