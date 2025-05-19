import json
from collections import defaultdict

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Seville': 6,
            'Paris': 2,
            'Krakow': 5
        }
        self.flights = {
            ('Krakow', 'Paris'): 1,
            ('Paris', 'Seville'): 1
        }
        self.workshop = {'Krakow': (1, 5)}

    def plan_trip(self):
        trip = []
        days = 0
        current_city = None
        for city, duration in self.cities.items():
            if city in self.workshop:
                start_day, end_day = self.workshop[city]
                trip.append({'day_range': f'Day {start_day}-{end_day}', 'place': city})
                days += end_day - start_day
            else:
                if current_city is not None:
                    for flight, duration in self.flights.items():
                        if flight[0] == current_city:
                            trip.append({'flying': f'Day {days}-{days}', 'from': current_city, 'to': flight[1]})
                            days += 1
                trip.append({'day_range': f'Day {days}-{days + duration - 1}', 'place': city})
                days += duration
                current_city = city
        if current_city is not None:
            for flight, duration in self.flights.items():
                if flight[0] == current_city:
                    trip.append({'flying': f'Day {days}-{days}', 'from': current_city, 'to': flight[1]})
                    days += 1
        return trip

    def output_json(self, trip):
        return json.dumps(trip, indent=4)

def main():
    planner = TripPlanner()
    trip = planner.plan_trip()
    print(planner.output_json(trip))

if __name__ == "__main__":
    main()