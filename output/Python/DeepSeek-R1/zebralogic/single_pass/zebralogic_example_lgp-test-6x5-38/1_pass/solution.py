import json

def main():
    # Define the solution based on deduction
    names = ['Alice', 'Arnold', 'Peter', 'Carol', 'Bob', 'Eric']
    birthdays = ['mar', 'sept', 'may', 'feb', 'april', 'jan']
    lunches = ['stir fry', 'spaghetti', 'grilled cheese', 'pizza', 'soup', 'stew']
    heights = ['short', 'average', 'super tall', 'very short', 'tall', 'very tall']
    cars = ['honda civic', 'bmw 3 series', 'chevrolet silverado', 'tesla model 3', 'ford f150', 'toyota camry']

    # Prepare the solution dictionary
    header = ["House", "Name", "Birthday Month", "Lunch", "Height", "Car Model"]
    rows = []
    for i in range(6):
        house_number = str(i+1)
        row = [house_number, names[i], birthdays[i], lunches[i], heights[i], cars[i]]
        rows.append(row)
    
    solution_dict = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    # Output the solution as JSON
    print(json.dumps(solution_dict, indent=2))

if __name__ == "__main__":
    main()