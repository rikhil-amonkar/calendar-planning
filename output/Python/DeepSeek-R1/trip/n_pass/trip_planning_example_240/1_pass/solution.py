import json

def main():
    durations = {
        'Prague': 2,
        'Stockholm': 5,
        'Berlin': 3,
        'Tallinn': 5
    }
    
    connections = {('Berlin', 'Tallinn'), ('Prague', 'Tallinn'),
                   ('Stockholm', 'Tallinn'), ('Prague', 'Stockholm'),
                   ('Stockholm', 'Berlin')}
    
    order = ['Prague', 'Stockholm', 'Berlin', 'Tallinn']
    
    valid_order = True
    for i in range(len(order) - 1):
        a, b = order[i], order[i+1]
        if (a, b) not in connections and (b, a) not in connections:
            valid_order = False
            break
    
    if not valid_order:
        result = {"error": "No valid itinerary found with given flight connections."}
    else:
        start = 1
        itinerary_list = []
        for city in order:
            end = start + durations[city] - 1
            day_range = f"Day {start}-{end}"
            itinerary_list.append({"day_range": day_range, "place": city})
            start = end
        result = {"itinerary": itinerary_list}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()