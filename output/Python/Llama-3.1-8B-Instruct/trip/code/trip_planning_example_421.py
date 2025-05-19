import json
from collections import defaultdict

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Nice': 5,
            'Krakow': 6,
            'Dublin': 7,
            'Lyon': 4,
            'Frankfurt': 2
        }
        self.flights = {
            ('Nice', 'Dublin'): 1,
            ('Dublin', 'Frankfurt'): 1,
            ('Dublin', 'Krakow'): 1,
            ('Krakow', 'Frankfurt'): 1,
            ('Lyon', 'Frankfurt'): 1,
            ('Nice', 'Frankfurt'): 1,
            ('Lyon', 'Dublin'): 1,
            ('Nice', 'Lyon'): 1
        }
        self.conference = {'Nice': (1, 5)}
        self.meeting = {'Frankfurt': (19, 20)}

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