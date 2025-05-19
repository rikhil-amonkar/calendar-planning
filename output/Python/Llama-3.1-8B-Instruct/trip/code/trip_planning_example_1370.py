import json
from collections import defaultdict

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Santorini': 5,
            'Krakow': 5,
            'Paris': 5,
            'Vilnius': 3,
            'Munich': 5,
            'Geneva': 2,
            'Amsterdam': 4,
            'Budapest': 5,
            'Split': 4
        }
        self.flights = {
            ('Paris', 'Krakow'): 1,
            ('Paris', 'Amsterdam'): 1,
            ('Paris', 'Split'): 1,
            ('Vilnius', 'Munich'): 1,
            ('Paris', 'Geneva'): 1,
            ('Amsterdam', 'Geneva'): 1,
            ('Munich', 'Split'): 1,
            ('Split', 'Krakow'): 1,
            ('Munich', 'Amsterdam'): 1,
            ('Budapest', 'Amsterdam'): 1,
            ('Split', 'Geneva'): 1,
            ('Vilnius', 'Split'): 1,
            ('Munich', 'Geneva'): 1,
            ('Munich', 'Krakow'): 1,
            ('Krakow', 'Vilnius'): 1,
            ('Vilnius', 'Amsterdam'): 1,
            ('Budapest', 'Paris'): 1,
            ('Krakow', 'Amsterdam'): 1,
            ('Vilnius', 'Paris'): 1,
            ('Budapest', 'Geneva'): 1,
            ('Split', 'Amsterdam'): 1,
            ('Santorini', 'Geneva'): 1,
            ('Amsterdam', 'Santorini'): 1,
            ('Munich', 'Budapest'): 1,
            ('Munich', 'Paris'): 1
        }
        self.conference = {'Krakow': (18, 22)}
        self.wedding = {'Krakow': (18, 22)}
        self.meeting = {'Paris': (11, 15), 'Santorini': (25, 29)}

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