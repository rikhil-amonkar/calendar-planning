import sys
sys.setrecursionlimit(10000)

def create_travel_graph():
    travel_graph = {
        'Paris': ['Amsterdam'],
        'Amsterdam': ['Paris', 'Berlin', 'Zurich'],
        'Berlin': ['Amsterdam', 'Prague'],
        'Prague': ['Berlin', 'Vienna'],
        'Vienna': ['Prague', 'Zurich', 'Milan'],
        'Zurich': ['Amsterdam', 'Vienna', 'Milan'],
        'Milan': ['Vienna', 'Zurich', 'Rome'],
        'Rome': ['Milan']
    }
    return travel_graph

city_activities = {
    'Paris': [1, 2],
    'Amsterdam': [3, 4],
    'Berlin': [5, 6],
    'Prague': [7, 8],
    'Vienna': [9, 10],
    'Zurich': [11, 12],
    'Milan': [13, 14],
    'Rome': [15, 16]
}

def dfs(current_city, day, itinerary, activities_done, city_activity_count, travel_graph):
    if day > 15:
        return None
    
    if day == 15:
        if current_city == 'Paris':
            return itinerary
        else:
            return None

    for activity in city_activities[current_city]:
        if activity in activities_done:
            continue
        if city_activity_count[current_city] >= 2:
            continue
            
        new_activities_done = set(activities_done)
        new_activities_done.add(activity)
        new_itinerary = list(itinerary)
        new_itinerary.append([day, current_city, activity])
        new_city_activity_count = dict(city_activity_count)
        new_city_activity_count[current_city] = new_city_activity_count.get(current_city, 0) + 1
        
        res = dfs(current_city, day + 1, new_itinerary, new_activities_done, new_city_activity_count, travel_graph)
        if res is not None:
            return res
            
        for next_city in travel_graph.get(current_city, []):
            new_itinerary = list(itinerary)
            new_itinerary.append([day, current_city, activity])
            new_activities_done = set(activities_done)
            new_activities_done.add(activity)
            new_city_activity_count = dict(city_activity_count)
            new_city_activity_count[current_city] = new_city_activity_count.get(current_city, 0) + 1
            
            res = dfs(next_city, day + 1, new_itinerary, new_activities_done, new_city_activity_count, travel_graph)
            if res is not None:
                return res
                
    return None

def main():
    travel_graph = create_travel_graph()
    start_city = 'Paris'
    itinerary = []
    activities_done = set()
    city_activity_count = {city: 0 for city in city_activities}
    
    result = dfs(start_city, 1, itinerary, activities_done, city_activity_count, travel_graph)
    
    if result is None:
        print("No solution found")
    else:
        for day, city, activity in result:
            print(f"[{day}, \"{city}\", \"Activity {activity}\"]")

if __name__ == "__main__":
    main()