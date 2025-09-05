import json

def compute_itinerary(order, durations):
    itinerary = []
    start_day = 1
    for city in order:
        finish_day = start_day + durations[city] - 1
        itinerary.append({"day_range": f"Day {start_day}-{finish_day}", "place": city})
        # Next city starts on the flight day, which is the finish day of the current city.
        start_day = finish_day
    return itinerary

def search(path, current_day, cities, durations, graph, directed_edges, total_days):
    if len(path) == len(cities):
        # If complete, current_day should equal total_days (the finish day of the last city)
        if current_day == total_days:
            return path
        else:
            return None
    for city in cities:
        if city in path:
            continue
        # Check direct flight connectivity from the last visited city if any.
        if path:
            last = path[-1]
            # Flight allowed if city is in the bidirectional graph or if a directed flight exists.
            if city not in graph[last] and (last, city) not in directed_edges:
                continue
        # Determine the start and finish day if we choose this city next.
        candidate_start = current_day
        candidate_finish = candidate_start + durations[city] - 1
        
        # Event constraint: Meet friend in Riga between day 4 and day 5.
        if city == "Riga":
            # Riga block covers candidate_start and candidate_start+1; acceptable if start is 3, 4, or 5.
            if candidate_start not in {3, 4, 5}:
                continue
                
        # Event constraint: Attend wedding in Dubrovnik between day 7 and day 8.
        if city == "Dubrovnik":
            # Dubrovnik block covers candidate_start and candidate_start+1; acceptable if start is 6, 7, or 8.
            if candidate_start not in {6, 7, 8}:
                continue
        
        new_path = path + [city]
        result = search(new_path, candidate_finish, cities, durations, graph, directed_edges, total_days)
        if result is not None:
            return result
    return None

def main():
    total_days = 18
    # List of cities we plan to visit.
    cities = ["Warsaw", "Riga", "Oslo", "Dubrovnik", "Madrid", "Lyon", "London", "Reykjavik"]
    durations = {
        "Reykjavik": 4,
        "Riga": 2,
        "Oslo": 3,
        "Lyon": 5,
        "Dubrovnik": 2,
        "Madrid": 2,
        "Warsaw": 4,
        "London": 3
    }
    # Define available direct flights.
    graph = {
        "Warsaw": {"Reykjavik", "Riga", "Oslo", "London", "Madrid"},
        "Reykjavik": {"Warsaw", "Oslo", "London"},
        "Riga": {"Warsaw", "Oslo"},
        "Oslo": {"Madrid", "Warsaw", "Reykjavik", "Dubrovnik", "Lyon", "London", "Riga"},
        "Lyon": {"London", "Oslo", "Madrid"},
        "Dubrovnik": {"Oslo", "Madrid"},
        "Madrid": {"Oslo", "Warsaw", "Lyon", "London", "Dubrovnik"},
        "London": {"Lyon", "Madrid", "Warsaw", "Oslo", "Reykjavik"}
    }
    # Add a directional flight: from Reykjavik to Madrid.
    directed_edges = {("Reykjavik", "Madrid")}
    
    itinerary_order = search([], 1, cities, durations, graph, directed_edges, total_days)
    
    if itinerary_order is None:
        output = {"itinerary": []}
    else:
        itinerary = compute_itinerary(itinerary_order, durations)
        output = {"itinerary": itinerary}
    
    print(json.dumps(output))
    
if __name__ == "__main__":
    main()