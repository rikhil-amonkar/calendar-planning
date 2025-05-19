import json
from collections import defaultdict

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Lyon': 3,
            'Paris': 5,
            'Riga': 2,
            'Berlin': 2,
            'Stockholm': 3,
            'Zurich': 5,
            'Nice': 2,
            'Seville': 3,
            'Milan': 3,
            'Naples': 4
        }
        self.flights = {
            ('Paris', 'Stockholm'): 1,
            ('Seville', 'Paris'): 1,
            ('Naples', 'Zurich'): 1,
            ('Nice', 'Riga'): 1,
            ('Berlin', 'Milan'): 1,
            ('Paris', 'Zurich'): 1,
            ('Paris', 'Nice'): 1,
            ('Milan', 'Paris'): 1,
            ('Milan', 'Riga'): 1,
            ('Paris', 'Lyon'): 1,
            ('Milan', 'Naples'): 1,
            ('Paris', 'Riga'): 1,
            ('Berlin', 'Stockholm'): 1,
            ('Stockholm', 'Riga'): 1,
            ('Nice', 'Zurich'): 1,
            ('Milan', 'Zurich'): 1,
            ('Lyon', 'Nice'): 1,
            ('Zurich', 'Stockholm'): 1,
            ('Zurich', 'Riga'): 1,
            ('Berlin', 'Naples'): 1,
            ('Milan', 'Stockholm'): 1,
            ('Berlin', 'Zurich'): 1,
            ('Milan', 'Seville'): 1,
            ('Paris', 'Naples'): 1,
            ('Berlin', 'Riga'): 1,
            ('Nice', 'Stockholm'): 1,
            ('Berlin', 'Paris'): 1,
            ('Nice', 'Naples'): 1,
            ('Berlin', 'Nice'): 1
        }
        self.wedding = {'Berlin': (1, 2)}
        self.conference = {'Stockholm': (20, 22)}
        self.workshop = {'Nice': (12, 13)}

    def plan_trip(self):
        trip = []
        days = 0
        current_city = None
        for city, duration in self.cities.items():
            if city in self.wedding:
                start_day, end_day = self.wedding[city]
                trip.append({'day_range': f'Day {start_day}-{end_day}', 'place': city})
                days += end_day - start_day
            elif city in self.conference:
                start_day, end_day = self.conference[city]
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