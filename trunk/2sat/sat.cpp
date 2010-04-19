#include <cassert>
#include <cstdio>
#include <cstring>
#include <vector>
#include <algorithm>
#include <utility>
#include <iostream>


const int N = 10000;

bool ok = true;
std::vector<int> impl[N];
int permval[N], tempval[N];
int asstime[N];
int current_time = 0;

int n, m;

bool incPropUnit(int x)
{
	if(permval[x] != 0)
	{
		if(permval[x] == 1)
			return true;
		else
		{
			ok = false;
			return false;
		}
	}

	permval[x] = 1;
	permval[x ^ 1] = -1;

	for(int i = 0; i < (int)impl[x].size(); i++)
		if(!incPropUnit(impl[x] [i]))
			return false;

	return true;
}

void incTempPropUnit(int x)
{
	if(tempval[x] == -1 && asstime[x ^ 1] == current_time)
	{
		incPropUnit(x);
		return;
	}

	tempval[x] = 1;
	tempval[x ^ 1] = -1;
	asstime[x] = current_time;
	asstime[x ^ 1] = current_time;

	for(int i = 0; ok && i < (int)impl[x].size() && permval[x] == 0; i++)
	{
		int y = impl[x] [i];
		if(permval[y] == 0 && !(asstime[y] == current_time && tempval[y] == 1))
			incTempPropUnit(y);
	}
}

bool incBinSat(int x, int y)
{
	impl[x ^ 1].push_back(y);
	impl[y ^ 1].push_back(x);


	current_time++;

	if(x == y)
		return incPropUnit(x);

	if(permval[x] == 1 || permval[y] == 1)
		return ok;

	if(permval[x] == -1)
		return incPropUnit(y);

	if(permval[y] == -1)
		return incPropUnit(x);

	if(tempval[x] == 1 || tempval[y] == 1)
		return ok;

	incTempPropUnit(x);
	return ok;
}


std::vector< std::pair<int, int> > clauses;

bool check()
{
	for(int i = 0; i < (int)clauses.size(); i++)
	{
		int a = clauses[i].first;
		int b = clauses[i].second;

		if(!((permval[a] == 1 || (permval[a] == 0 && tempval[a] == 1)) || (permval[b] == 1 || (permval[b] == 0 && tempval[b] == 1))))
			return false;
	}
	return true;
}

int main()
{
	freopen("input.txt", "r", stdin);
	freopen("output.txt", "w", stdout);

	scanf("%i %i", &n, &m);
	for(int i = 0; i < m; i++)
	{
		int a, b;
		scanf("%i %i", &a, &b);

		assert(a != 0);
		if(b == 0)
			b = a;
		else
		{
			int tmp;
			scanf("%i", &tmp);
			assert(tmp == 0);
		}

		if(a < 0)
			a = 2 * (-a - 1) + 1;
		else
			a = 2 * (a - 1);

		if(b < 0)
			b = 2 * (-b - 1) + 1;
		else
			b = 2 * (b - 1);

		clauses.push_back(std::make_pair(a, b));

		incBinSat(a, b);
	}

	if(ok)
	{
		assert(check());

		printf("Yes\n");

		for(int i = 0; i < n; i++)
			if(permval[2 * i] == 1)
				printf("%i ", i + 1);
			else if(permval[2 * i] == 0 && tempval[2 * i] == 1)
				printf("%i ", i + 1);

		printf("0\n");
	}
	else
	{
		printf("No\n");
	}

	return 0;
}
