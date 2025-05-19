import json
from collections import defaultdict

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Reykjavik': 4,
            'Riga': 2,
            'Oslo': 3,
            'Lyon': 5,
            'Dubrovnik': 2,
            'Madrid': 2,
            'Warsaw': 4,
            'London': 3
        }
        self.flights = {
            ('Warsaw', 'Reykjavik'): 1,
            ('Oslo', 'Madrid'): 1,
            ('Warsaw', 'Riga'): 1,
            ('Lyon', 'London'): 1,
            ('Madrid', 'London'): 1,
            ('Warsaw', 'London'): 1,
            ('Reykjavik', 'Madrid'): 1,
            ('Warsaw', 'Oslo'): 1,
            ('Oslo', 'Dubrovnik'): 1,
            ('Oslo', 'Reykjavik'): 1,
            ('Riga', 'Oslo'): 1,
            ('Oslo', 'Lyon'): 1,
            ('Oslo', 'London'): 1,
            ('London', 'Reykjavik'): 1,
            ('Warsaw', 'Madrid'): 1,
            ('Madrid', 'Lyon'): 1,
            ('Dubrovnik', 'Madrid'): 1
        }
        self.conference = {'Riga': (4, 5)}
        self.wedding = {'Dubrovnik': (7, 8)}
        self.meeting = {'Riga': (4, 5)}

    def plan_trip(self):
        trip = []
        days = 0
        current_city = None
        for city, duration in self.cities.items():
            if city in self.conference:
                start_day, end_day = self.conference[city]
                trip.append({'day_range': f'Day {start_day}-{end_day}', 'place': city})
                days += end_day - start_day
            elif city in self.wedding:
                start_day, end_day = self.wedding[city]
                trip.append({'day_range': f'Day {start_day}-{end_day}', 'place': city})
                days += end_day - start_day
            elif city in self.meeting:
                start_day, end_day = self.meeting[city]
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