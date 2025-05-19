import json
from collections import defaultdict

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Vienna': 4,
            'Lyon': 3,
            'Edinburgh': 4,
            'Reykjavik': 5,
            'Stuttgart': 5,
            'Manchester': 2,
            'Split': 5,
            'Prague': 4
        }
        self.flights = {
            ('Reykjavik', 'Stuttgart'): 1,
            ('Stuttgart', 'Split'): 1,
            ('Stuttgart', 'Vienna'): 1,
            ('Prague', 'Manchester'): 1,
            ('Edinburgh', 'Prague'): 1,
            ('Manchester', 'Split'): 1,
            ('Prague', 'Split'): 1,
            ('Vienna', 'Manchester'): 1,
            ('Prague', 'Lyon'): 1,
            ('Stuttgart', 'Edinburgh'): 1,
            ('Split', 'Lyon'): 1,
            ('Stuttgart', 'Manchester'): 1,
            ('Prague', 'Lyon'): 1,
            ('Reykjavik', 'Vienna'): 1,
            ('Prague', 'Reykjavik'): 1,
            ('Vienna', 'Split'): 1
        }
        self.conference = {'Edinburgh': (5, 8)}
        self.wedding = {'Split': (19, 23)}

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