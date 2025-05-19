#!/usr/bin/env python3
import json

def main():
    # Input parameters:
    
    # Total days:
    total_days = 25

    # Cities with required days:
    # Note: When traveling from one city to the next on a flight day, that day counts for both cities.
    # Thus total tour days = sum(required_days) - (number_of_flights)
    # There are 9 cities so number_of_flights = 8.
    # Our constraints sum to 33 days so 33 - 8 = 25 days total.
    #
    # Cities and required durations:
    #  - Oslo: 2 days (with a friend meeting on day 24-25)
    #  - Helsinki: 2 days
    #  - Edinburgh: 3 days
    #  - Riga: 2 days
    #  - Tallinn: 5 days (includes a wedding between day 4 and day 8)
    #  - Budapest: 5 days
    #  - Vilnius: 5 days
    #  - Porto: 5 days
    #  - Geneva: 4 days
    #
    # Direct flights available:
    #   Porto <--> Oslo, Edinburgh <--> Budapest, Edinburgh <--> Geneva, Riga -> Tallinn,
    #   Edinburgh <--> Porto, Vilnius <--> Helsinki, Tallinn -> Vilnius, Riga <--> Oslo,
    #   Geneva <--> Oslo, Edinburgh <--> Oslo, Edinburgh <--> Helsinki,
    #   Vilnius <--> Oslo, Riga <--> Helsinki, Budapest <--> Geneva, Helsinki <--> Budapest,
    #   Helsinki <--> Oslo, Edinburgh <--> Riga, Tallinn <--> Helsinki, Geneva <--> Porto,
    #   Budapest <--> Oslo, Helsinki <--> Geneva, Riga -> Vilnius, Tallinn <--> Oslo.
    #
    # Based on these connections and the time constraints (including the wedding and friend meeting),
    # we choose the following itinerary order:
    # 
    # 1. Edinburgh (3 days)  [Days 1 - 3]
    #    Flight from Edinburgh to Riga ("Edinburgh and Riga")
    # 2. Riga (2 days)       [Overlapping day: day 3, then day 4]
    #    Flight from Riga to Tallinn ("from Riga to Tallinn")
    # 3. Tallinn (5 days)    [Starts day 4 until day 8, covering the wedding event]
    #    Flight from Tallinn to Vilnius ("from Tallinn to Vilnius")
    # 4. Vilnius (5 days)    [Days 8 - 12]
    #    Flight from Vilnius to Helsinki ("Vilnius and Helsinki")
    # 5. Helsinki (2 days)   [Days 12 - 13]
    #    Flight from Helsinki to Budapest ("Helsinki and Budapest")
    # 6. Budapest (5 days)   [Days 13 - 17]
    #    Flight from Budapest to Geneva ("Budapest and Geneva")
    # 7. Geneva (4 days)     [Days 17 - 20]
    #    Flight from Geneva to Porto ("Geneva and Porto")
    # 8. Porto (5 days)      [Days 20 - 24]
    #    Flight from Porto to Oslo ("Porto and Oslo")
    # 9. Oslo (2 days)       [Days 24 - 25, friend meeting occurs on day 24 or 25]
    #
    # This ordering meets all direct flight constraints and the specific event constraints.
    
    itinerary = [
        {"place": "Edinburgh", "days": 3},
        {"place": "Riga", "days": 2},
        {"place": "Tallinn", "days": 5},   # Wedding between day 4 and 8 falls here.
        {"place": "Vilnius", "days": 5},
        {"place": "Helsinki", "days": 2},
        {"place": "Budapest", "days": 5},
        {"place": "Geneva", "days": 4},
        {"place": "Porto", "days": 5},
        {"place": "Oslo", "days": 2}       # Friend meeting in Oslo must occur on day 24 or 25.
    ]
    
    # Calculation of day ranges using the overlapping day rule:
    #
    # If we denote city[i]'s required duration as d_i and assume:
    #   start_day[0] = 1
    #   end_day[0] = start_day[0] + d_0 - 1
    # For each subsequent city i > 0:
    #   start_day[i] = end_day[i-1]   (because the flight day counts in both)
    #   end_day[i] = start_day[i] + d_i - 1
    #
    schedule = []
    current_day = 1
    for city in itinerary:
        place = city["place"]
        d = city["days"]
        start_day = current_day
        end_day = start_day + d - 1
        # Append the schedule entry with the required keys
        schedule.append({
            "day_range": f"{start_day}-{end_day}",
            "place": place
        })
        # Prepare next city's start day: flight day is same as current end_day.
        current_day = end_day

    # Validate total days equal 25:
    if current_day != total_days:
        raise ValueError(f"Calculated itinerary spans {current_day} days; expected {total_days} days.")
        
    # Output the schedule as JSON formatted string (list of dictionaries with only day_range and place)
    json_output = json.dumps(schedule, indent=2)
    print(json_output)

if __name__ == '__main__':
    main()