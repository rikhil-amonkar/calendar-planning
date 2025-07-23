import itertools
import json

def main():
    days_dict = {
        'Rome': 3,
        'Mykonos': 2,
        'Lisbon': 2,
        'Frankfurt': 5,
        'Nice': 3,
        'Stuttgart': 4,
        'Venice': 4,
        'Dublin': 2,
        'Bucharest': 2,
        'Seville': 5
    }
    
    flights = [
        "Rome and Stuttgart", 
        "Venice and Rome", 
        "Dublin and Bucharest", 
        "Mykonos and Rome", 
        "Seville and Lisbon", 
        "Frankfurt and Venice", 
        "Venice and Stuttgart", 
        "Bucharest and Lisbon", 
        "Nice and Mykonos", 
        "Venice and Lisbon", 
        "Dublin and Lisbon", 
        "Venice and Nice", 
        "Rome and Seville", 
        "Frankfurt and Rome", 
        "Nice and Dublin", 
        "Rome and Bucharest", 
        "Frankfurt and Dublin", 
        "Rome and Dublin", 
        "Venice and Dublin", 
        "Rome and Lisbon", 
        "Frankfurt and Lisbon", 
        "Nice and Rome", 
        "Frankfurt and Nice", 
        "Frankfurt and Stuttgart", 
        "Frankfurt and Bucharest", 
        "Lisbon and Stuttgart", 
        "Nice and Lisbon", 
        "Seville and Dublin"
    ]
    
    graph = set()
    for flight in flights:
        parts = flight.split(' and ')
        city1, city2 = parts[0], parts[1]
        edge = tuple(sorted([city1, city2]))
        graph.add(edge)
    
    def are_connected(c1, c2):
        return tuple(sorted([c1, c2])) in graph
        
    cities = list(days_dict.keys())
    solution_found = False
    solution_perm = None
    solution_ends = None
    solution_T0 = None
    
    for perm in itertools.permutations(cities):
        valid = True
        for i in range(len(perm)-1):
            if not are_connected(perm[i], perm[i+1]):
                valid = False
                break
        if not valid:
            continue
        
        T0 = days_dict[perm[0]]
        ends = [0] * 9
        if len(perm) > 1:
            ends[0] = T0 + days_dict[perm[1]] - 1
            for i in range(2, 9):
                ends[i] = ends[i-1] + days_dict[perm[i]] - 1
        else:
            ends = [T0] * 9
            
        last_city = perm[9]
        last_block_length = 24 - ends[8]
        if last_block_length != days_dict[last_city]:
            continue
        
        try:
            j = perm.index('Seville')
        except ValueError:
            continue
        
        if j == 0:
            start_seville = 1
        elif j == 1:
            start_seville = T0
        else:
            start_seville = ends[j-2]
        if start_seville != 13:
            continue
        
        try:
            k = perm.index('Mykonos')
        except ValueError:
            continue
        
        if k == 0:
            start_mykonos = 1
        elif k == 1:
            start_mykonos = T0
        else:
            start_mykonos = ends[k-2]
        if start_mykonos > 11:
            continue
        
        try:
            l = perm.index('Frankfurt')
        except ValueError:
            continue
        
        if l > 0:
            if l == 1:
                start_frankfurt = T0
            else:
                start_frankfurt = ends[l-2]
            if start_frankfurt > 5:
                continue
        
        solution_found = True
        solution_perm = perm
        solution_ends = ends
        solution_T0 = T0
        break
    
    if not solution_found:
        print(json.dumps({"itinerary": []}))
        return
    
    itinerary_list = []
    for i, city in enumerate(solution_perm):
        if i == 0:
            start_day = 1
            end_day = solution_T0
        elif i < 9:
            start_day = solution_ends[i-1]
            end_day = solution_ends[i]
        else:
            start_day = solution_ends[8]
            end_day = 23
        day_range_str = f"Day {start_day}-{end_day}"
        itinerary_list.append({"day_range": day_range_str, "place": city})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()