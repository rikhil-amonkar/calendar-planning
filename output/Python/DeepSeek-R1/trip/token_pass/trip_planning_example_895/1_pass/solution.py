import itertools
import json

def main():
    # Define the graph of direct flights
    graph = {
        'Brussels': ['Venice', 'London', 'Lisbon', 'Reykjavik', 'Madrid'],
        'Venice': ['Madrid', 'Brussels', 'Santorini', 'Lisbon', 'London'],
        'London': ['Brussels', 'Madrid', 'Santorini', 'Reykjavik', 'Lisbon', 'Venice'],
        'Lisbon': ['Reykjavik', 'Venice', 'Brussels', 'London', 'Madrid'],
        'Reykjavik': ['Lisbon', 'Madrid', 'London', 'Brussels'],
        'Santorini': ['Venice', 'London', 'Madrid'],
        'Madrid': ['Venice', 'Reykjavik', 'London', 'Santorini', 'Lisbon', 'Brussels']
    }
    
    # Define the required days for each city
    required_days = {
        'Brussels': 2,
        'Venice': 3,
        'London': 3,
        'Lisbon': 4,
        'Reykjavik': 3,
        'Santorini': 3,
        'Madrid': 5
    }
    
    cities = ['Brussels', 'Venice', 'London', 'Lisbon', 'Reykjavik', 'Santorini', 'Madrid']
    other_cities = cities[1:]
    
    for perm in itertools.permutations(other_cities):
        sequence = ['Brussels'] + list(perm)
        valid_sequence = True
        for i in range(len(sequence) - 1):
            if sequence[i+1] not in graph[sequence[i]]:
                valid_sequence = False
                break
        if not valid_sequence:
            continue
            
        arrival = [0] * 7
        departure = [0] * 7
        arrival[0] = 1
        departure[0] = arrival[0] + required_days[sequence[0]] - 1
        
        for i in range(1, 7):
            arrival[i] = departure[i-1]
            departure[i] = arrival[i] + required_days[sequence[i]] - 1
            
        if departure[6] != 17:
            continue
            
        venice_index = sequence.index('Venice')
        madrid_index = sequence.index('Madrid')
        
        if not (arrival[venice_index] <= 7 and departure[venice_index] >= 5):
            continue
            
        if not (arrival[madrid_index] <= 11 and departure[madrid_index] >= 7):
            continue
            
        itinerary = []
        for i in range(7):
            start = arrival[i]
            end = departure[i]
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": sequence[i]})
            
        result = {"itinerary": itinerary}
        print(json.dumps(result))
        return
        
    print('{"itinerary": []}')

if __name__ == "__main__":
    main()