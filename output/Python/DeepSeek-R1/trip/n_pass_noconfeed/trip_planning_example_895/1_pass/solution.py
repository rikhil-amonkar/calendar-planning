import json

def build_flight_graph():
    graph = {
        'Brussels': set(['Venice', 'London', 'Lisbon', 'Reykjavik', 'Madrid']),
        'London': set(['Brussels', 'Madrid', 'Santorini', 'Reykjavik', 'Lisbon']),
        'Lisbon': set(['Reykjavik', 'Venice', 'Brussels', 'London', 'Madrid']),
        'Reykjavik': set(['Lisbon', 'London']),
        'Santorini': set(['Venice', 'London', 'Madrid']),
        'Venice': set(['Brussels', 'Santorini', 'Lisbon', 'London', 'Madrid']),
        'Madrid': set(['Venice', 'London', 'Santorini', 'Lisbon'])
    }
    return graph

def main():
    segments = [
        (1, 2, 'Brussels'),
        (2, 5, 'Lisbon'),
        (5, 7, 'Venice'),
        (7, 11, 'Madrid')
    ]
    
    flight_graph = build_flight_graph()
    
    next_city = 'Madrid'
    remaining_cities = ['Santorini', 'London', 'Reykjavik']
    current_city = next_city
    
    if 'Santorini' in flight_graph[current_city]:
        segments.append((11, 13, 'Santorini'))
        current_city = 'Santorini'
        if 'London' in flight_graph[current_city]:
            segments.append((13, 15, 'London'))
            current_city = 'London'
            if 'Reykjavik' in flight_graph[current_city]:
                segments.append((15, 17, 'Reykjavik'))
            else:
                print("No flight from London to Reykjavik")
                return
        else:
            print("No flight from Santorini to London")
            return
    else:
        print("No flight from Madrid to Santorini")
        return
    
    itinerary_list = []
    for start, end, city in segments:
        day_range_str = f"Day {start}-{end}"
        itinerary_list.append({"day_range": day_range_str, "place": city})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()