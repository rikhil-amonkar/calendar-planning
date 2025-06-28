import json

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
        total_days = 0
        visited_cities = set()

        while total_days < 18:
            itinerary.append({'day_range': f"Day {day}-{day + self.durations[current_city] - 1}", 'place': current_city})
            day += self.durations[current_city]
            total_days += self.durations[current_city]
            visited_cities.add(current_city)

            next_cities = [city for city in self.transitions[current_city] if city not in visited_cities]
            if next_cities:
                next_city = max(next_cities, key=lambda city: self.transitions[current_city][city])
                transition = self.transitions[current_city][next_city]
                if day + transition - 1 <= 18:
                    itinerary.append({'day_range': f"Day {day}-{day + transition - 1}", 'place': next_city})
                    day += transition
                    total_days += transition
                    current_city = next_city

        # Adjust the itinerary to cover exactly 18 days
        while total_days < 18:
            next_cities = [city for city in self.transitions[current_city] if city not in visited_cities]
            if next_cities:
                next_city = max(next_cities, key=lambda city: self.transitions[current_city][city])
                transition = self.transitions[current_city][next_city]
                if day + transition - 1 <= 18:
                    itinerary.append({'day_range': f"Day {day}-{day + transition - 1}", 'place': next_city})
                    day += transition
                    total_days += transition
                    current_city = next_city

        return {'itinerary': [{'day_range': f"Day {item['day_range'].split('-')[0]}-{item['day_range'].split('-')[1]}", 'place': item['place']} for item in itinerary]}

def main():
    trip_planner = TripPlanner()
    result = trip_planner.compute_itinerary()
    print(json.dumps(result, indent=4))

if __name__ == "__main__":
    main()