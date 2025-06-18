def main():
    # Define the itinerary based on the calculated travel days
    plan = [
        (1, ['Dublin']),
        (2, ['Dublin', 'Riga']),
        (3, ['Riga']),
        (4, ['Riga']),
        (5, ['Riga']),
        (6, ['Riga', 'Vilnius']),
        (7, ['Vilnius']),
        (8, ['Vilnius']),
        (9, ['Vilnius']),
        (10, ['Vilnius']),
        (11, ['Vilnius']),
        (12, ['Vilnius'])
    ]
    
    for day, cities in plan:
        print(f"Day {day}: {', '.join(cities)}")

if __name__ == '__main__':
    main()