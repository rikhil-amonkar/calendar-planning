import json
from typing import List, Dict, Tuple

class TripPlanner:
    def __init__(self):
        # Direct flight connections (undirected graph)
        self.flights = {
            'London': ['Hamburg', 'Reykjavik', 'Stuttgart', 'Barcelona', 
                      'Bucharest', 'Zurich', 'Stockholm', 'Milan'],
            'Hamburg': ['London', 'Stockholm', 'Bucharest', 'Milan', 
                       'Stuttgart', 'Zurich', 'Barcelona'],
            'Milan': ['Barcelona', 'Zurich', 'Hamburg', 'Stockholm', 
                     'Stuttgart', 'Reykjavik', 'London'],
            'Reykjavik': ['London', 'Barcelona', 'Stuttgart', 'Stockholm', 
                         'Milan', 'Zurich'],
            'Barcelona': ['Milan', 'Reykjavik', 'London', 'Stockholm', 
                         'Tallinn', 'Hamburg', 'Stuttgart', 'Zurich', 'Bucharest'],
            'Zurich': ['Milan', 'London', 'Hamburg', 'Barcelona', 
                      'Stockholm', 'Tallinn', 'Reykjavik', 'Bucharest'],
            'Stockholm': ['Reykjavik', 'Hamburg', 'Stuttgart', 'Tallinn', 
                         'Milan', 'London', 'Barcelona', 'Zurich'],
            'Stuttgart': ['London', 'Reykjavik', 'Stockholm', 'Milan', 
                         'Hamburg', 'Barcelona'],
            'Bucharest': ['Hamburg', 'London', 'Barcelona', 'Zurich'],
            'Tallinn': ['Stockholm', 'Barcelona', 'Zurich']
        }
        
        # Required days in each city
        self.required_days = {
            'Zurich': 2,
            'Bucharest': 2,
            'Hamburg': 5,
            'Barcelona': 4,
            'Reykjavik': 5,
            'Stuttgart': 5,
            'Stockholm': 2,
            'Tallinn': 4,
            'Milan': 5,
            'London': 3
        }
        
        # Fixed schedule constraints
        self.fixed_schedule = {
            1: 'London',   # Day 1-3: London
            2: 'London',
            3: 'London',
            4: 'Milan',    # Day 4-7: Milan (note: day 3 is travel day from London to Milan)
            5: 'Milan',
            6: 'Milan',
            7: 'Milan',
            8: 'Zurich',   # Day 7-8: Zurich (day 7 is travel from Milan to Zurich)
            9: 'Zurich',
            10: 'Reykjavik', # Day 9-13: Reykjavik (day 9 is travel from Zurich to Reykjavik)
            11: 'Reykjavik',
            12: 'Reykjavik',
            13: 'Reykjavik',
            14: 'Reykjavik'
        }
        
        # Initialize with fixed schedule
        self.schedule = {}
        for day in range(1, 29):
            if day in self.fixed_schedule:
                self.schedule[day] = self.fixed_schedule[day]
    
    def is_connected(self, city1: str, city2: str) -> bool:
        """Check if there's a direct flight between two cities."""
        return city2 in self.flights.get(city1, [])
    
    def count_days_per_city(self) -> Dict[str, int]:
        """Count how many days are spent in each city."""
        counts = {city: 0 for city in self.required_days}
        for day in range(1, 29):
            city = self.schedule.get(day)
            if city:
                counts[city] += 1
        return counts
    
    def find_available_city(self, current_city: str, visited: set, remaining_days: Dict[str, int]) -> str:
        """Find a city to visit next based on connections and remaining required days."""
        possible_cities = []
        
        for city in self.flights[current_city]:
            if city not in visited and remaining_days.get(city, 0) > 0:
                possible_cities.append(city)
        
        # If no unvisited cities with remaining days, consider visited ones
        if not possible_cities:
            for city in self.flights[current_city]:
                if remaining_days.get(city, 0) > 0:
                    possible_cities.append(city)
        
        # Sort by remaining days (descending) to prioritize cities needing more days
        possible_cities.sort(key=lambda x: remaining_days.get(x, 0), reverse=True)
        
        return possible_cities[0] if possible_cities else None
    
    def fill_schedule(self):
        """Fill the remaining days in the schedule."""
        # Count current days per city
        current_counts = self.count_days_per_city()
        
        # Calculate remaining days needed for each city
        remaining_needed = {}
        for city, required in self.required_days.items():
            remaining = required - current_counts.get(city, 0)
            if remaining > 0:
                remaining_needed[city] = remaining
        
        # Start from day 14 (after fixed schedule)
        current_day = 14
        current_city = 'Reykjavik'  # Last city in fixed schedule
        visited_cities = set(self.schedule.values())
        
        while current_day <= 28 and remaining_needed:
            # Find next city to visit
            next_city = self.find_available_city(current_city, visited_cities, remaining_needed)
            
            if not next_city:
                # If no city found, stay in current city
                next_city = current_city
            
            # Check if we can reach next city
            if next_city != current_city and not self.is_connected(current_city, next_city):
                # Find an intermediate city
                for city in self.flights[current_city]:
                    if city in self.flights[next_city]:
                        next_city = city
                        break
            
            # Determine how many days to spend in next city
            days_to_spend = min(
                remaining_needed.get(next_city, 0),
                28 - current_day + 1
            )
            
            if days_to_spend <= 0:
                days_to_spend = 1
            
            # Fill the schedule
            for i in range(days_to_spend):
                if current_day > 28:
                    break
                self.schedule[current_day] = next_city
                current_day += 1
            
            # Update counts
            if next_city in remaining_needed:
                remaining_needed[next_city] -= days_to_spend
                if remaining_needed[next_city] <= 0:
                    del remaining_needed[next_city]
            
            # Update current city and visited cities
            current_city = next_city
            visited_cities.add(current_city)
    
    def optimize_schedule(self):
        """Optimize the schedule to ensure all requirements are met."""
        # First pass: fill schedule
        self.fill_schedule()
        
        # Check if all requirements are met
        final_counts = self.count_days_per_city()
        
        # Adjust if needed
        for city, required in self.required_days.items():
            if final_counts.get(city, 0) < required:
                # Find where we can add days for this city
                for day in range(1, 29):
                    if self.schedule.get(day) != city:
                        # Check if we can change this day to the needed city
                        prev_city = self.schedule.get(day - 1, city)
                        next_city = self.schedule.get(day + 1, city)
                        
                        if (self.is_connected(prev_city, city) and 
                            self.is_connected(city, next_city)):
                            self.schedule[day] = city
                            final_counts = self.count_days_per_city()
                            if final_counts.get(city, 0) >= required:
                                break
    
    def create_itinerary_output(self) -> List[Dict]:
        """Convert schedule to itinerary format with day ranges."""
        itinerary = []
        current_city = None
        start_day = 1
        
        for day in range(1, 29):
            city = self.schedule.get(day)
            
            if not city:
                # Fill any missing days with previous city
                city = current_city if current_city else 'London'
                self.schedule[day] = city
            
            if city != current_city:
                if current_city is not None:
                    itinerary.append({
                        'day_range': f'Day {start_day}-{day-1}',
                        'place': current_city
                    })
                current_city = city
                start_day = day
        
        # Add the last segment
        itinerary.append({
            'day_range': f'Day {start_day}-28',
            'place': current_city
        })
        
        return itinerary
    
    def validate_itinerary(self) -> bool:
        """Validate that all constraints are met."""
        # Check total days
        if len(self.schedule) != 28:
            return False
        
        # Check required days per city
        counts = self.count_days_per_city()
        for city, required in self.required_days.items():
            if counts.get(city, 0) < required:
                print(f"City {city} has {counts.get(city, 0)} days but needs {required}")
                return False
        
        # Check flight connections
        for day in range(2, 29):
            city1 = self.schedule.get(day - 1)
            city2 = self.schedule.get(day)
            if city1 != city2 and not self.is_connected(city1, city2):
                print(f"No direct flight from {city1} to {city2} on day {day}")
                return False
        
        # Check fixed constraints
        for day, expected_city in self.fixed_schedule.items():
            if self.schedule.get(day) != expected_city:
                print(f"Day {day} should be {expected_city} but is {self.schedule.get(day)}")
                return False
        
        return True

def main():
    planner = TripPlanner()
    planner.optimize_schedule()
    
    if planner.validate_itinerary():
        itinerary = planner.create_itinerary_output()
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("Error: Could not create valid itinerary")

if __name__ == "__main__":
    main()