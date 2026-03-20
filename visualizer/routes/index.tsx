import { Handlers, PageProps } from "$fresh/server.ts";
import examples from "../lib/examples.ts";
import App from "../islands/App.tsx";

export type Example = { name: string; code: string };

export const handler: Handlers<Example[]> = {
  GET(_req, ctx) {
    return ctx.render(examples);
  },
};

export default function Home({ data }: PageProps<Example[]>) {
  return <App examples={data} />;
}
