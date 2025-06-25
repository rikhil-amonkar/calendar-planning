import itertools
import json

def main():
    graph = {
        'Brussels': ['Venice', 'London', 'Lisbon', 'Reykjavik', 'Madrid'],
        'Venice': ['Madrid', 'Brussels', 'Santorini', 'Lisbon', 'London'],
        'London': ['Brussels', 'Madrid', 'Santorini', 'Reykjavik', 'Lisbon', 'Venice'],
        'Lisbon': ['Reykjavik', 'Venice', 'London', 'Madrid', 'Brussels'],
        'Reykjavik': ['Lisbon', 'Madrid', 'London', 'Brussels'],
        'Santorini': ['Venice', 'London', 'Madrid'],
        'Madrid': ['Venice', 'Reykjavik', 'London', 'Lisbon', 'Santorini', 'Brussels']
    }
    
    durations = {
        'Brussels': 2,
        'Venice': 3,
        'London': 3,
        'Lisbon': 4,
        'Reykjavik': 3,
        'Santorini': 3,
        'Madrid': 5
    }
    
    cities = ['Venice', 'London', 'Lisbon', 'Reykjavik', 'Santorini', 'Madrid']
    
    for perm in itertools.permutations(cities):
        seq = ['Brussels'] + list(perm)
        valid_sequence = True
        for i in range(len(seq) - 1):
            if seq[i+1] not in graph[seq[i]]:
                valid_sequence = False
                break
        if not valid_sequence:
            continue
            
        start_days = [1]
        for i in range(1, 7):
            next_start = start_days[i-1] + durations[seq[i-1]] - 1
            start_days.append(next_start)
        
        venice_index = seq.index('Venice')
        venice_start = start_days[venice_index]
        if venice_start < 3 or venice_start > 7:
            continue
            
        madrid_index = seq.index('Madrid')
        madrid_start = start_days[madrid_index]
        if madrid_start < 3 or madrid_start > 11:
            continue
            
        itinerary = []
        for i in range(7):
            start = start_days[i]
            end = start + durations[seq[i]] - 1
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({
                "day_range": day_range,
                "place": seq[i]
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
        return
    
    print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == '__main__':
    main()