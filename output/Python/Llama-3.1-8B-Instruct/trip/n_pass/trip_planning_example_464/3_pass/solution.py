import json
from collections import defaultdict

class TripPlanner:
    def __init__(self):
        self.cities = ['Krakow', 'Frankfurt', 'Oslo', 'Dubrovnik', 'Naples']
        self.durations = {'Krakow': 5, 'Frankfurt': 4, 'Oslo': 3, 'Dubrovnik': 5, 'Naples': 5}
        self.transitions = {
            'Krakow': {'Frankfurt': 4, 'Oslo': 3},
            'Frankfurt': {'Krakow': 4, 'Oslo': 3, 'Dubrovnik': 2},
            'Oslo': {'Krakow': 3, 'Frankfurt': 3, 'Dubrovnik': 4, 'Naples': 2},
            'Dubrovnik': {'Frankfurt': 2, 'Naples': 4},
            'Naples': {'Oslo': 2, 'Dubrovnik': 4}
        }
        self.relative_visit = (16, 18)
        self.friend_visit = (5, 9)

    def compute_itinerary(self):
        itinerary = []
        current_city = 'Krakow'
        day = 1
        for city, duration in self.durations.items():
            itinerary.append({'day_range': f"Day {day}-{day + duration - 1}", 'place': city})
            day += duration
            current_city = city

        for city, transitions in self.transitions.items():
            if current_city!= city:
                for next_city, transition in transitions.items():
                    if next_city!= current_city:
                        if (day + transition - 1) > self.relative_visit[1] or (day + transition - 1) > self.friend_visit[1]:
                            itinerary.append({'day_range': f"Day {day}-{day + transition - 1}", 'place': next_city})
                            day += transition
                            current_city = next_city

        return {'itinerary': [{'day_range': f"Day {item['day_range'].split('-')[0]}-{item['day_range'].split('-')[1]}", 'place': item['place']} for item in itinerary]}

def main():
    trip_planner = TripPlanner()
    result = trip_planner.compute_itinerary()
    print(json.dumps(result, indent=4))

if __name__ == "__main__":
    main()