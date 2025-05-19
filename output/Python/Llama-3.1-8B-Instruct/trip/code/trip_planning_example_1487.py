import json
from collections import defaultdict

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Copenhagen': 5,
            'Geneva': 3,
            'Mykonos': 2,
            'Naples': 4,
            'Prague': 2,
            'Dubrovnik': 3,
            'Athens': 4,
            'Santorini': 5,
            'Brussels': 4,
            'Munich': 5
        }
        self.flights = {
            ('Copenhagen', 'Dubrovnik'): 1,
            ('Brussels', 'Copenhagen'): 1,
            ('Prague', 'Geneva'): 1,
            ('Athens', 'Geneva'): 1,
            ('Naples', 'Dubrovnik'): 1,
            ('Athens', 'Dubrovnik'): 1,
            ('Geneva', 'Mykonos'): 1,
            ('Naples', 'Mykonos'): 1,
            ('Naples', 'Copenhagen'): 1,
            ('Munich', 'Mykonos'): 1,
            ('Naples', 'Athens'): 1,
            ('Prague', 'Athens'): 1,
            ('Santorini', 'Geneva'): 1,
            ('Athens', 'Santorini'): 1,
            ('Naples', 'Munich'): 1,
            ('Prague', 'Copenhagen'): 1,
            ('Brussels', 'Naples'): 1,
            ('Athens', 'Mykonos'): 1,
            ('Athens', 'Copenhagen'): 1,
            ('Naples', 'Geneva'): 1,
            ('Dubrovnik', 'Munich'): 1,
            ('Brussels', 'Munich'): 1,
            ('Prague', 'Brussels'): 1,
            ('Brussels', 'Athens'): 1,
            ('Athens', 'Munich'): 1,
            ('Geneva', 'Munich'): 1,
            ('Copenhagen', 'Munich'): 1,
            ('Brussels', 'Geneva'): 1,
            ('Copenhagen', 'Geneva'): 1,
            ('Prague', 'Munich'): 1,
            ('Copenhagen', 'Santorini'): 1,
            ('Naples', 'Santorini'): 1,
            ('Geneva', 'Dubrovnik'): 1
        }
        self.conference = {'Mykonos': (27, 28)}
        self.meeting = {'Copenhagen': (11, 15)}
        self.workshop = {'Athens': (8, 11)}

    def plan_trip(self):
        trip = []
        days = 0
        current_city = None
        for city, duration in self.cities.items():
            if city in self.conference:
                start_day, end_day = self.conference[city]
                trip.append({'day_range': f'Day {start_day}-{end_day}', 'place': city})
                days += end_day - start_day
            elif city in self.meeting:
                start_day, end_day = self.meeting[city]
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