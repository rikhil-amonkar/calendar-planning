import json
from collections import defaultdict

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Manchester': 3,
            'Istanbul': 7,
            'Venice': 7,
            'Krakow': 6,
            'Lyon': 2
        }
        self.flights = {
            ('Manchester', 'Venice'): 1,
            ('Manchester', 'Istanbul'): 1,
            ('Venice', 'Istanbul'): 1,
            ('Istanbul', 'Krakow'): 1,
            ('Venice', 'Lyon'): 1,
            ('Lyon', 'Istanbul'): 1,
            ('Manchester', 'Krakow'): 1
        }
        self.wedding = {'Manchester': (1, 3)}
        self.workshop = {'Venice': (3, 9)}

    def plan_trip(self):
        trip = []
        days = 0
        current_city = None
        for city, duration in self.cities.items():
            if city in self.wedding:
                start_day, end_day = self.wedding[city]
                trip.append({'day_range': f'Day {start_day}-{end_day}', 'place': city})
                days += end_day - start_day
            elif city in self.workshop:
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