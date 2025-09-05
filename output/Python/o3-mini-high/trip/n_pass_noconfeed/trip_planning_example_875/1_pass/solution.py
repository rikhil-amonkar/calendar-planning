import itertools
import json

def main():
    # Define each city's required duration (in days)
    cities = {
        "Stuttgart": 3,
        "Edinburgh": 4,
        "Athens": 4,
        "Split": 2,
        "Krakow": 4,
        "Venice": 5,
        "Mykonos": 4
    }
    
    # Meeting constraints as (window_start, window_end)
    meeting_constraints = {
        "Stuttgart": (11, 13),  # Workshop must occur between day 11 and day 13
        "Krakow": (8, 11),      # Meet friend in Krakow between day 8 and day 11
        "Split": (13, 14)       # Meet friend in Split between day 13 and day 14
    }
    
    # Define the flight connectivity graph (bidirectional edges)
    flight_graph = {
        "Krakow": {"Split", "Edinburgh", "Stuttgart"},
        "Split": {"Krakow", "Athens", "Stuttgart"},
        "Edinburgh": {"Krakow", "Stuttgart", "Venice", "Athens"},
        "Stuttgart": {"Venice", "Krakow", "Edinburgh", "Athens", "Split"},
        "Athens": {"Split", "Stuttgart", "Venice", "Mykonos", "Edinburgh"},
        "Venice": {"Stuttgart", "Edinburgh", "Athens"},
        "Mykonos": {"Athens"}
    }
    
    city_list = list(cities.keys())
    valid_itinerary = None

    # Check if consecutive cities in the order have a direct flight connection.
    def is_connected(order):
        for i in range(len(order) - 1):
            if order[i+1] not in flight_graph[order[i]]:
                return False
        return True

    # Compute the schedule given an order.
    # If a city is visited with a duration d, the itinerary is defined so that:
    #   For the first city: days [1, d].
    #   For each subsequent city, its start day equals the previous city's end day (flight day counted for both).
    def compute_schedule(order):
        schedule = []
        day = 1
        for city in order:
            start = day
            end = start + cities[city] - 1
            schedule.append({"city": city, "start": start, "end": end})
            day = end  # Next city starts on the overlapping flight day.
        return schedule

    # Check if each schedule that has a meeting requirement overlaps with its meeting window.
    def satisfies_meeting(schedule):
        for entry in schedule:
            city = entry["city"]
            start = entry["start"]
            end = entry["end"]
            if city in meeting_constraints:
                m_start, m_end = meeting_constraints[city]
                # The visit interval [start, end] must overlap with the meeting window [m_start, m_end]
                if end < m_start or start > m_end:
                    return False
        return True

    # Iterate through all possible orders (permutations) of visiting the 7 cities.
    for perm in itertools.permutations(city_list):
        # Only consider orders where every consecutive flight is directly connected.
        if not is_connected(perm):
            continue
        
        schedule = compute_schedule(perm)
        # Total unique days must sum to 20. (Sum(durations) - (# transfers)) = 26 - 6 = 20.
        if schedule[-1]["end"] != 20:
            continue
        
        if not satisfies_meeting(schedule):
            continue
        
        valid_itinerary = schedule
        break

    # Format the itinerary for JSON output.
    if valid_itinerary is None:
        result = {"itinerary": []}
    else:
        itinerary_output = []
        for entry in valid_itinerary:
            day_range = f"Day {entry['start']}-{entry['end']}"
            itinerary_output.append({"day_range": day_range, "place": entry["city"]})
        result = {"itinerary": itinerary_output}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()